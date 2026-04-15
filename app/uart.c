/* Copyright 2023 Dual Tachyon
 * https://github.com/DualTachyon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 *     Unless required by applicable law or agreed to in writing, software
 *     distributed under the License is distributed on an "AS IS" BASIS,
 *     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *     See the License for the specific language governing permissions and
 *     limitations under the License.
 */

#include <string.h>

#if !defined(ENABLE_OVERLAY)
	#include "ARMCM0.h"
#endif
#ifdef ENABLE_FMRADIO
	#include "app/fm.h"
#endif
#include "app/uart.h"
#include "board.h"
#include "bsp/dp32g030/dma.h"
#include "bsp/dp32g030/gpio.h"
#include "driver/aes.h"
#include "driver/backlight.h"
#include "driver/bk4819.h"
#include "driver/crc.h"
#include "driver/eeprom.h"
#include "driver/gpio.h"
#include "driver/uart.h"
#include "functions.h"
#include "misc.h"
#include "radio.h"
#include "settings.h"
#include "version.h"

#if defined(ENABLE_OVERLAY)
	#include "sram-overlay.h"
#endif


#define DMA_INDEX(x, y) (((x) + (y)) % sizeof(UART_DMA_Buffer))

typedef struct {
	uint16_t ID;
	uint16_t Size;
} Header_t;

typedef struct {
	uint8_t  Padding[2];
	uint16_t ID;
} Footer_t;

typedef struct {
	Header_t Header;
	uint32_t Timestamp;
} CMD_0514_t;

typedef struct {
	Header_t Header;
	struct {
		char     Version[16];
		bool     bHasCustomAesKey;
		bool     bIsInLockScreen;
		uint8_t  Padding[2];
		uint32_t Challenge[4];
	} Data;
} REPLY_0514_t;

typedef struct {
	Header_t Header;
	uint16_t Offset;
	uint8_t  Size;
	uint8_t  Padding;
	uint32_t Timestamp;
} CMD_051B_t;

typedef struct {
	Header_t Header;
	struct {
		uint16_t Offset;
		uint8_t  Size;
		uint8_t  Padding;
		uint8_t  Data[128];
	} Data;
} REPLY_051B_t;

typedef struct {
	Header_t Header;
	uint16_t Offset;
	uint8_t  Size;
	bool     bAllowPassword;
	uint32_t Timestamp;
	uint8_t  Data[0];
} CMD_051D_t;

typedef struct {
	Header_t Header;
	struct {
		uint16_t Offset;
	} Data;
} REPLY_051D_t;

typedef struct {
	Header_t Header;
	struct {
		uint16_t RSSI;
		uint8_t  ExNoiseIndicator;
		uint8_t  GlitchIndicator;
	} Data;
} REPLY_0527_t;

typedef struct {
	Header_t Header;
	struct {
		uint16_t Voltage;
		uint16_t Current;
	} Data;
} REPLY_0529_t;

typedef struct {
	Header_t Header;
	uint32_t Response[4];
} CMD_052D_t;

typedef struct {
	Header_t Header;
	struct {
		bool bIsLocked;
		uint8_t Padding[3];
	} Data;
} REPLY_052D_t;

typedef struct {
	Header_t Header;
	uint32_t Timestamp;
} CMD_052F_t;

static const uint8_t Obfuscation[16] =
{
	0x16, 0x6C, 0x14, 0xE6, 0x2E, 0x91, 0x0D, 0x40, 0x21, 0x35, 0xD5, 0x40, 0x13, 0x03, 0xE9, 0x80
};

static union
{
	uint8_t Buffer[256];
	struct
	{
		Header_t Header;
		uint8_t Data[252];
	};
} UART_Command;

static uint32_t Timestamp;
static uint16_t gUART_WriteIndex;
static bool     bIsEncrypted  = true;
static bool     bIsCATCommand = false;
static char     CAT_Buffer[16];
static uint8_t  CAT_Length;

// ---- CAT helper functions ----

// Write 'digits' zero-padded decimal digits of 'val' into buf (no null terminator)
static void cat_fmt_uint(char *buf, uint32_t val, uint8_t digits)
{
	buf += digits;
	while (digits--) {
		*--buf = (char)('0' + (uint8_t)(val % 10u));
		val /= 10u;
	}
}

// Kenwood CAT mode number <-> firmware modulation
static uint8_t cat_mod_to_cat(ModulationMode_t m)
{
	switch (m) {
		case MODULATION_USB: return 2;
		case MODULATION_AM:  return 5;
		default:             return 4; // FM
	}
}

static ModulationMode_t cat_cat_to_mod(uint8_t c)
{
	switch (c) {
		case 2:  return MODULATION_USB;
		case 5:  return MODULATION_AM;
		default: return MODULATION_FM;
	}
}

// Send plain ASCII reply (no binary framing, no encryption)
static void cat_reply(const char *s, uint8_t len)
{
	UART_Send(s, len);
}

// Parse 11 ASCII decimal digits starting at s into Hz, returns 0 on bad input
static uint32_t cat_parse_freq(const char *s)
{
	uint32_t hz = 0;
	for (uint8_t i = 0; i < 11; i++) {
		if (s[i] < '0' || s[i] > '9')
			return 0;
		hz = hz * 10u + (uint32_t)(s[i] - '0');
	}
	return hz;
}

// Set VFO frequency (in 10 Hz units) and trigger retune
static void cat_set_vfo_freq(uint8_t vfo, uint32_t freq_10hz)
{
	gEeprom.VfoInfo[vfo].freq_config_RX.Frequency = freq_10hz;
	gEeprom.VfoInfo[vfo].freq_config_TX.Frequency = freq_10hz;
	gEeprom.VfoInfo[vfo].pRX = &gEeprom.VfoInfo[vfo].freq_config_RX;
	gEeprom.VfoInfo[vfo].pTX = &gEeprom.VfoInfo[vfo].freq_config_TX;
	gFlagReconfigureVfos  = true;
	gVfoConfigureMode     = VFO_CONFIGURE;
}

static void HandleCATCommand(void)
{
	const char *cmd = CAT_Buffer;
	char        buf[40];

	// ID - radio identification (Kenwood TS-480 compatible)
	if (cmd[0]=='I' && cmd[1]=='D' && cmd[2]=='\0') {
		cat_reply("ID019;", 6);
		return;
	}

	// PS - power status (radio is on by definition)
	if (cmd[0]=='P' && cmd[1]=='S' && cmd[2]=='\0') {
		cat_reply("PS1;", 4);
		return;
	}

	// AI - auto information (acknowledge, stub)
	if (cmd[0]=='A' && cmd[1]=='I') {
		cat_reply("AI0;", 4);
		return;
	}

	// RX - return to receive
	if (cmd[0]=='R' && cmd[1]=='X' && cmd[2]=='\0') {
		if (gCurrentFunction == FUNCTION_TRANSMIT) {
			gFlagEndTransmission = true;
			FUNCTION_Select(FUNCTION_FOREGROUND);
		}
		cat_reply("RX0;", 4);
		return;
	}

	// TX / TX0 - start transmit
	if (cmd[0]=='T' && cmd[1]=='X' && (cmd[2]=='\0' || cmd[2]=='0')) {
		gFlagPrepareTX = true;
		cat_reply("TX0;", 4);
		return;
	}

	// FA - VFO A frequency (11-digit Hz)
	if (cmd[0]=='F' && cmd[1]=='A') {
		if (cmd[2]=='\0') {
			buf[0]='F'; buf[1]='A';
			cat_fmt_uint(buf+2, gEeprom.VfoInfo[0].pRX->Frequency * 10u, 11);
			buf[13]=';';
			cat_reply(buf, 14);
		} else {
			uint32_t hz = cat_parse_freq(cmd+2);
			if (hz)
				cat_set_vfo_freq(0, hz / 10u);
		}
		return;
	}

	// FB - VFO B frequency (11-digit Hz)
	if (cmd[0]=='F' && cmd[1]=='B') {
		if (cmd[2]=='\0') {
			buf[0]='F'; buf[1]='B';
			cat_fmt_uint(buf+2, gEeprom.VfoInfo[1].pRX->Frequency * 10u, 11);
			buf[13]=';';
			cat_reply(buf, 14);
		} else {
			uint32_t hz = cat_parse_freq(cmd+2);
			if (hz)
				cat_set_vfo_freq(1, hz / 10u);
		}
		return;
	}

	// MD - mode (1/3=FM, 2=USB, 4=FM, 5=AM)
	if (cmd[0]=='M' && cmd[1]=='D') {
		if (cmd[2]=='\0') {
			buf[0]='M'; buf[1]='D';
			buf[2]=(char)('0' + cat_mod_to_cat(gTxVfo->Modulation));
			buf[3]=';';
			cat_reply(buf, 4);
		} else {
			RADIO_SetModulation(cat_cat_to_mod((uint8_t)(cmd[2] - '0')));
			gFlagReconfigureVfos = true;
			gVfoConfigureMode    = VFO_CONFIGURE;
		}
		return;
	}

	// IF - current operating information (Kenwood TS-480 format)
	// IF[11-freq][5-passband][±][5-RIT][RIT-on][XIT-on][2-bank][3-mem][TX][mode][VFO][scan][split][tone];
	if (cmd[0]=='I' && cmd[1]=='F' && cmd[2]=='\0') {
		uint8_t mode = cat_mod_to_cat(gTxVfo->Modulation);
		uint8_t tx   = (gCurrentFunction == FUNCTION_TRANSMIT) ? 1u : 0u;
		buf[0]='I'; buf[1]='F';
		cat_fmt_uint(buf+2,  gTxVfo->pRX->Frequency * 10u, 11); // P1 freq
		buf[13]=' '; buf[14]=' '; buf[15]=' '; buf[16]=' '; buf[17]=' '; // P2 passband
		buf[18]='+';                                                       // P3 RIT sign
		buf[19]='0'; buf[20]='0'; buf[21]='0'; buf[22]='0'; buf[23]='0'; // P3 RIT value
		buf[24]='0';                                                       // P4 RIT off
		buf[25]='0';                                                       // P5 XIT off
		buf[26]='0'; buf[27]='0';                                          // P6 bank
		buf[28]='0'; buf[29]='0'; buf[30]='0';                            // P7 mem ch
		buf[31]=(char)('0'+tx);                                            // P8 TX/RX
		buf[32]=(char)('0'+mode);                                          // P9 mode
		buf[33]='0';                                                       // P10 VFO
		buf[34]='0';                                                       // P11 scan
		buf[35]='0';                                                       // P12 split
		buf[36]='0';                                                       // P13 tone
		buf[37]=';';
		cat_reply(buf, 38);
		return;
	}

	// SM - S-meter / signal strength (0-30 scale, Kenwood SM0XXXX; format)
	if (cmd[0]=='S' && cmd[1]=='M') {
		uint16_t rssi = BK4819_ReadRegister(BK4819_REG_67) & 0x01FFu;
		uint16_t sm   = (rssi > 200u) ? 30u : (uint16_t)((rssi * 30u) / 200u);
		buf[0]='S'; buf[1]='M'; buf[2]='0';
		cat_fmt_uint(buf+3, sm, 4);
		buf[7]=';';
		cat_reply(buf, 8);
		return;
	}

	// FR - select receive VFO (FR0=VFO-A, FR1=VFO-B)
	if (cmd[0]=='F' && cmd[1]=='R') {
		if (cmd[2]=='\0') {
			buf[0]='F'; buf[1]='R';
			buf[2]=(char)('0' + gEeprom.RX_VFO);
			buf[3]=';';
			cat_reply(buf, 4);
		} else {
			uint8_t vfo = (uint8_t)(cmd[2] - '0');
			if (vfo <= 1u) {
				gEeprom.RX_VFO = vfo;
				RADIO_SelectVfos();
				gFlagReconfigureVfos = true;
				gVfoConfigureMode    = VFO_CONFIGURE;
			}
		}
		return;
	}

	// FT - select transmit VFO (FT0=VFO-A, FT1=VFO-B)
	if (cmd[0]=='F' && cmd[1]=='T') {
		if (cmd[2]=='\0') {
			buf[0]='F'; buf[1]='T';
			buf[2]=(char)('0' + gEeprom.TX_VFO);
			buf[3]=';';
			cat_reply(buf, 4);
		} else {
			uint8_t vfo = (uint8_t)(cmd[2] - '0');
			if (vfo <= 1u) {
				gEeprom.TX_VFO = vfo;
				RADIO_SelectVfos();
				gFlagReconfigureVfos = true;
				gVfoConfigureMode    = VFO_CONFIGURE;
			}
		}
		return;
	}

	// SQ - squelch level (SQ0[0-9]; maps to firmware squelch 0-9)
	if (cmd[0]=='S' && cmd[1]=='Q') {
		if (cmd[2]=='\0' || cmd[2]=='0') {
			if (cmd[2]=='\0' || cmd[3]=='\0') {
				// read
				buf[0]='S'; buf[1]='Q'; buf[2]='0';
				buf[3]=(char)('0' + (gEeprom.SQUELCH_LEVEL & 0x0Fu));
				buf[4]=';';
				cat_reply(buf, 5);
			} else {
				// write: SQ0[digit]
				uint8_t level = (uint8_t)(cmd[3] - '0');
				if (level <= 9u) {
					gEeprom.SQUELCH_LEVEL = level;
					gFlagReconfigureVfos  = true;
					gVfoConfigureMode     = VFO_CONFIGURE;
				}
			}
		}
		return;
	}

	// AG - AF gain / volume (AG0[000-255];)
	if (cmd[0]=='A' && cmd[1]=='G') {
		if (cmd[2]=='\0' || (cmd[2]=='0' && cmd[3]=='\0')) {
			// read
			buf[0]='A'; buf[1]='G'; buf[2]='0';
			cat_fmt_uint(buf+3, gEeprom.VOLUME_GAIN, 3);
			buf[6]=';';
			cat_reply(buf, 7);
		} else if (cmd[2]=='0' && cmd[3]!='\0') {
			// write: AG0[3-digit value]
			uint32_t val = 0;
			for (uint8_t i = 0; i < 3; i++) {
				if (cmd[3+i] < '0' || cmd[3+i] > '9') return;
				val = val * 10u + (uint32_t)(cmd[3+i] - '0');
			}
			if (val > 255u) val = 255u;
			gEeprom.VOLUME_GAIN = (uint8_t)val;
		}
		return;
	}

	// PC - TX power level (PC[3-digit]; maps LOW=005, MID=010, HIGH=050)
	if (cmd[0]=='P' && cmd[1]=='C') {
		if (cmd[2]=='\0') {
			// read: map OUTPUT_POWER to approximate watts
			static const uint16_t pc_watts[3] = {5u, 10u, 50u};
			uint8_t pwr = gTxVfo->OUTPUT_POWER;
			if (pwr > 2u) pwr = 2u;
			buf[0]='P'; buf[1]='C';
			cat_fmt_uint(buf+2, pc_watts[pwr], 3);
			buf[5]=';';
			cat_reply(buf, 6);
		} else {
			// write: set power level based on value
			uint32_t val = 0;
			for (uint8_t i = 0; i < 3; i++) {
				if (cmd[2+i] < '0' || cmd[2+i] > '9') return;
				val = val * 10u + (uint32_t)(cmd[2+i] - '0');
			}
			gTxVfo->OUTPUT_POWER = (val <= 7u)  ? OUTPUT_POWER_LOW  :
			                       (val <= 25u) ? OUTPUT_POWER_MID  :
			                                      OUTPUT_POWER_HIGH;
			gFlagReconfigureVfos = true;
			gVfoConfigureMode    = VFO_CONFIGURE;
		}
		return;
	}

	// RA - RF attenuator (stub — hardware has none, always return off)
	if (cmd[0]=='R' && cmd[1]=='A') {
		cat_reply("RA00;", 5);
		return;
	}

	// VV - VFO A = VFO B (copy A into B)
	if (cmd[0]=='V' && cmd[1]=='V' && cmd[2]=='\0') {
		gEeprom.VfoInfo[1] = gEeprom.VfoInfo[0];
		gEeprom.VfoInfo[1].pRX = &gEeprom.VfoInfo[1].freq_config_RX;
		gEeprom.VfoInfo[1].pTX = &gEeprom.VfoInfo[1].freq_config_TX;
		gFlagReconfigureVfos = true;
		gVfoConfigureMode    = VFO_CONFIGURE;
		return;
	}

	// Unknown command — reply with '?' so software doesn't hang waiting
	cat_reply("?;", 2);
}

static void SendReply(void *pReply, uint16_t Size)
{
	Header_t Header;
	Footer_t Footer;

	if (bIsEncrypted)
	{
		uint8_t     *pBytes = (uint8_t *)pReply;
		unsigned int i;
		for (i = 0; i < Size; i++)
			pBytes[i] ^= Obfuscation[i % 16];
	}

	Header.ID = 0xCDAB;
	Header.Size = Size;
	UART_Send(&Header, sizeof(Header));
	UART_Send(pReply, Size);

	if (bIsEncrypted)
	{
		Footer.Padding[0] = Obfuscation[(Size + 0) % 16] ^ 0xFF;
		Footer.Padding[1] = Obfuscation[(Size + 1) % 16] ^ 0xFF;
	}
	else
	{
		Footer.Padding[0] = 0xFF;
		Footer.Padding[1] = 0xFF;
	}
	Footer.ID = 0xBADC;

	UART_Send(&Footer, sizeof(Footer));
}

static void SendVersion(void)
{
	REPLY_0514_t Reply;

	Reply.Header.ID = 0x0515;
	Reply.Header.Size = sizeof(Reply.Data);
	strcpy(Reply.Data.Version, Version);
	Reply.Data.bHasCustomAesKey = bHasCustomAesKey;
	Reply.Data.bIsInLockScreen = bIsInLockScreen;
	Reply.Data.Challenge[0] = gChallenge[0];
	Reply.Data.Challenge[1] = gChallenge[1];
	Reply.Data.Challenge[2] = gChallenge[2];
	Reply.Data.Challenge[3] = gChallenge[3];

	SendReply(&Reply, sizeof(Reply));
}

static bool IsBadChallenge(const uint32_t *pKey, const uint32_t *pIn, const uint32_t *pResponse)
{
	unsigned int i;
	uint32_t     IV[4];

	IV[0] = 0;
	IV[1] = 0;
	IV[2] = 0;
	IV[3] = 0;

	AES_Encrypt(pKey, IV, pIn, IV, true);

	for (i = 0; i < 4; i++)
		if (IV[i] != pResponse[i])
			return true;

	return false;
}

// session init, sends back version info and state
// timestamp is a session id really
static void CMD_0514(const uint8_t *pBuffer)
{
	const CMD_0514_t *pCmd = (const CMD_0514_t *)pBuffer;

	Timestamp = pCmd->Timestamp;

	#ifdef ENABLE_FMRADIO
		gFmRadioCountdown_500ms = fm_radio_countdown_500ms;
	#endif

	gSerialConfigCountDown_500ms = 12; // 6 sec
	
	// turn the LCD backlight off
	BACKLIGHT_TurnOff();

	SendVersion();
}

// read eeprom
static void CMD_051B(const uint8_t *pBuffer)
{
	const CMD_051B_t *pCmd = (const CMD_051B_t *)pBuffer;
	REPLY_051B_t      Reply;
	bool              bLocked = false;

	if (pCmd->Timestamp != Timestamp)
		return;

	gSerialConfigCountDown_500ms = 12; // 6 sec

	#ifdef ENABLE_FMRADIO
		gFmRadioCountdown_500ms = fm_radio_countdown_500ms;
	#endif

	memset(&Reply, 0, sizeof(Reply));
	Reply.Header.ID   = 0x051C;
	Reply.Header.Size = pCmd->Size + 4;
	Reply.Data.Offset = pCmd->Offset;
	Reply.Data.Size   = pCmd->Size;

	if (bHasCustomAesKey)
		bLocked = gIsLocked;

	if (!bLocked)
		EEPROM_ReadBuffer(pCmd->Offset, Reply.Data.Data, pCmd->Size);

	SendReply(&Reply, pCmd->Size + 8);
}

// write eeprom
static void CMD_051D(const uint8_t *pBuffer)
{
	const CMD_051D_t *pCmd = (const CMD_051D_t *)pBuffer;
	REPLY_051D_t Reply;
	bool bReloadEeprom;
	bool bIsLocked;

	if (pCmd->Timestamp != Timestamp)
		return;

	gSerialConfigCountDown_500ms = 12; // 6 sec
	
	bReloadEeprom = false;

	#ifdef ENABLE_FMRADIO
		gFmRadioCountdown_500ms = fm_radio_countdown_500ms;
	#endif

	Reply.Header.ID   = 0x051E;
	Reply.Header.Size = sizeof(Reply.Data);
	Reply.Data.Offset = pCmd->Offset;

	bIsLocked = bHasCustomAesKey ? gIsLocked : bHasCustomAesKey;

	if (!bIsLocked)
	{
		unsigned int i;
		for (i = 0; i < (pCmd->Size / 8); i++)
		{
			const uint16_t Offset = pCmd->Offset + (i * 8U);

			if (Offset >= 0x0F30 && Offset < 0x0F40)
				if (!gIsLocked)
					bReloadEeprom = true;

			if ((Offset < 0x0E98 || Offset >= 0x0EA0) || !bIsInLockScreen || pCmd->bAllowPassword)
				EEPROM_WriteBuffer(Offset, &pCmd->Data[i * 8U]);
		}

		if (bReloadEeprom)
			SETTINGS_InitEEPROM();
	}

	SendReply(&Reply, sizeof(Reply));
}

// read RSSI
static void CMD_0527(void)
{
	REPLY_0527_t Reply;

	Reply.Header.ID             = 0x0528;
	Reply.Header.Size           = sizeof(Reply.Data);
	Reply.Data.RSSI             = BK4819_ReadRegister(BK4819_REG_67) & 0x01FF;
	Reply.Data.ExNoiseIndicator = BK4819_ReadRegister(BK4819_REG_65) & 0x007F;
	Reply.Data.GlitchIndicator  = BK4819_ReadRegister(BK4819_REG_63);

	SendReply(&Reply, sizeof(Reply));
}

// read ADC
static void CMD_0529(void)
{
	REPLY_0529_t Reply;

	Reply.Header.ID   = 0x52A;
	Reply.Header.Size = sizeof(Reply.Data);

	// Original doesn't actually send current!
	BOARD_ADC_GetBatteryInfo(&Reply.Data.Voltage, &Reply.Data.Current);

	SendReply(&Reply, sizeof(Reply));
}

static void CMD_052D(const uint8_t *pBuffer)
{
	const CMD_052D_t *pCmd = (const CMD_052D_t *)pBuffer;
	REPLY_052D_t      Reply;
	bool              bIsLocked;

	#ifdef ENABLE_FMRADIO
		gFmRadioCountdown_500ms = fm_radio_countdown_500ms;
	#endif
	Reply.Header.ID   = 0x052E;
	Reply.Header.Size = sizeof(Reply.Data);

	bIsLocked = bHasCustomAesKey;

	if (!bIsLocked)
		bIsLocked = IsBadChallenge(gCustomAesKey, gChallenge, pCmd->Response);

	if (!bIsLocked)
	{
		bIsLocked = IsBadChallenge(gDefaultAesKey, gChallenge, pCmd->Response);
		if (bIsLocked)
			gTryCount++;
	}

	if (gTryCount < 3)
	{
		if (!bIsLocked)
			gTryCount = 0;
	}
	else
	{
		gTryCount = 3;
		bIsLocked = true;
	}
	
	gIsLocked            = bIsLocked;
	Reply.Data.bIsLocked = bIsLocked;

	SendReply(&Reply, sizeof(Reply));
}

// session init, sends back version info and state
// timestamp is a session id really
// this command also disables dual watch, crossband, 
// DTMF side tones, freq reverse, PTT ID, DTMF decoding, frequency offset
// exits power save, sets main VFO to upper,
static void CMD_052F(const uint8_t *pBuffer)
{
	const CMD_052F_t *pCmd = (const CMD_052F_t *)pBuffer;

	gEeprom.DUAL_WATCH                               = DUAL_WATCH_OFF;
	gEeprom.CROSS_BAND_RX_TX                         = CROSS_BAND_OFF;
	gEeprom.RX_VFO                                   = 0;
	gEeprom.DTMF_SIDE_TONE                           = false;
	gEeprom.VfoInfo[0].FrequencyReverse              = false;
	gEeprom.VfoInfo[0].pRX                           = &gEeprom.VfoInfo[0].freq_config_RX;
	gEeprom.VfoInfo[0].pTX                           = &gEeprom.VfoInfo[0].freq_config_TX;
	gEeprom.VfoInfo[0].TX_OFFSET_FREQUENCY_DIRECTION = TX_OFFSET_FREQUENCY_DIRECTION_OFF;
	gEeprom.VfoInfo[0].DTMF_PTT_ID_TX_MODE           = PTT_ID_OFF;
#ifdef ENABLE_DTMF_CALLING
	gEeprom.VfoInfo[0].DTMF_DECODING_ENABLE          = false;
#endif

	#ifdef ENABLE_NOAA
		gIsNoaaMode = false;
	#endif

	if (gCurrentFunction == FUNCTION_POWER_SAVE)
		FUNCTION_Select(FUNCTION_FOREGROUND);

	gSerialConfigCountDown_500ms = 12; // 6 sec

	Timestamp = pCmd->Timestamp;

	// turn the LCD backlight off
	BACKLIGHT_TurnOff();

	SendVersion();
}

#ifdef ENABLE_UART_RW_BK_REGS
static void CMD_0601_ReadBK4819Reg(const uint8_t *pBuffer)
{
	typedef struct  __attribute__((__packed__)) {
		Header_t header;
		uint8_t reg;
	} CMD_0601_t;

	CMD_0601_t *cmd = (CMD_0601_t*) pBuffer;

	struct __attribute__((__packed__)) {
		Header_t header;
		struct __attribute__((__packed__)) {
			uint8_t reg;
			uint16_t value;
		} data;
	} reply;

	reply.header.ID = 0x0601;
	reply.header.Size = sizeof(reply.data);
	reply.data.reg = cmd->reg;
	reply.data.value = BK4819_ReadRegister(cmd->reg);
	SendReply(&reply, sizeof(reply));
}

static void CMD_0602_WriteBK4819Reg(const uint8_t *pBuffer)
{
	typedef struct __attribute__((__packed__)) {
		Header_t header;
		uint8_t reg;
		uint16_t value;
	} CMD_0602_t;

	CMD_0602_t *cmd = (CMD_0602_t*) pBuffer;
	BK4819_WriteRegister(cmd->reg, cmd->value);
}
#endif

bool UART_IsCommandAvailable(void)
{
	uint16_t Index;
	uint16_t TailIndex;
	uint16_t Size;
	uint16_t CRC;
	uint16_t CommandLength;
	uint16_t DmaLength = DMA_CH0->ST & 0xFFFU;

	bIsCATCommand = false;

	// Skip null bytes left by previous commands
	while (gUART_WriteIndex != DmaLength && UART_DMA_Buffer[gUART_WriteIndex] == 0)
		gUART_WriteIndex = DMA_INDEX(gUART_WriteIndex, 1);

	if (gUART_WriteIndex == DmaLength)
		return false;

	// ASCII CAT command detection: starts with an uppercase letter
	if (UART_DMA_Buffer[gUART_WriteIndex] >= 'A' && UART_DMA_Buffer[gUART_WriteIndex] <= 'Z')
	{
		uint16_t scan   = gUART_WriteIndex;
		uint8_t  catLen = 0;

		while (scan != DmaLength && catLen <= 13)
		{
			uint8_t c = UART_DMA_Buffer[scan];
			if (c == ';')
			{
				if (catLen >= 2)
				{
					// Valid — extract command bytes (without ';')
					uint16_t rd = gUART_WriteIndex;
					uint8_t  j  = 0;
					while (rd != scan) {
						CAT_Buffer[j++] = (char)UART_DMA_Buffer[rd];
						UART_DMA_Buffer[rd] = 0;
						rd = DMA_INDEX(rd, 1);
					}
					CAT_Buffer[j]    = '\0';
					CAT_Length       = j;
					UART_DMA_Buffer[scan] = 0;
					gUART_WriteIndex = DMA_INDEX(scan, 1);
					bIsCATCommand    = true;
					return true;
				}
				// Too short — discard
				gUART_WriteIndex = DMA_INDEX(scan, 1);
				return false;
			}
			catLen++;
			scan = DMA_INDEX(scan, 1);
		}
		// No ';' found yet — wait for more data
		return false;
	}

	while (1)
	{
		if (gUART_WriteIndex == DmaLength)
			return false;

		while (gUART_WriteIndex != DmaLength && UART_DMA_Buffer[gUART_WriteIndex] != 0xABU)
			gUART_WriteIndex = DMA_INDEX(gUART_WriteIndex, 1);

		if (gUART_WriteIndex == DmaLength)
			return false;

		if (gUART_WriteIndex < DmaLength)
			CommandLength = DmaLength - gUART_WriteIndex;
		else
			CommandLength = (DmaLength + sizeof(UART_DMA_Buffer)) - gUART_WriteIndex;

		if (CommandLength < 8)
			return 0;

		if (UART_DMA_Buffer[DMA_INDEX(gUART_WriteIndex, 1)] == 0xCD)
			break;

		gUART_WriteIndex = DMA_INDEX(gUART_WriteIndex, 1);
	}

	Index = DMA_INDEX(gUART_WriteIndex, 2);
	Size  = (UART_DMA_Buffer[DMA_INDEX(Index, 1)] << 8) | UART_DMA_Buffer[Index];

	if ((Size + 8u) > sizeof(UART_DMA_Buffer))
	{
		gUART_WriteIndex = DmaLength;
		return false;
	}

	if (CommandLength < (Size + 8))
		return false;

	Index     = DMA_INDEX(Index, 2);
	TailIndex = DMA_INDEX(Index, Size + 2);

	if (UART_DMA_Buffer[TailIndex] != 0xDC || UART_DMA_Buffer[DMA_INDEX(TailIndex, 1)] != 0xBA)
	{
		gUART_WriteIndex = DmaLength;
		return false;
	}

	if (TailIndex < Index)
	{
		const uint16_t ChunkSize = sizeof(UART_DMA_Buffer) - Index;
		memcpy(UART_Command.Buffer, UART_DMA_Buffer + Index, ChunkSize);
		memcpy(UART_Command.Buffer + ChunkSize, UART_DMA_Buffer, TailIndex);
	}
	else
		memcpy(UART_Command.Buffer, UART_DMA_Buffer + Index, TailIndex - Index);

	TailIndex = DMA_INDEX(TailIndex, 2);
	if (TailIndex < gUART_WriteIndex)
	{
		memset(UART_DMA_Buffer + gUART_WriteIndex, 0, sizeof(UART_DMA_Buffer) - gUART_WriteIndex);
		memset(UART_DMA_Buffer, 0, TailIndex);
	}
	else
		memset(UART_DMA_Buffer + gUART_WriteIndex, 0, TailIndex - gUART_WriteIndex);

	gUART_WriteIndex = TailIndex;

	if (UART_Command.Header.ID == 0x0514)
		bIsEncrypted = false;

	if (UART_Command.Header.ID == 0x6902)
		bIsEncrypted = true;

	if (bIsEncrypted)
	{
		unsigned int i;
		for (i = 0; i < (Size + 2u); i++)
			UART_Command.Buffer[i] ^= Obfuscation[i % 16];
	}
	
	CRC = UART_Command.Buffer[Size] | (UART_Command.Buffer[Size + 1] << 8);

	return (CRC_Calculate(UART_Command.Buffer, Size) != CRC) ? false : true;
}

void UART_HandleCommand(void)
{
	if (bIsCATCommand) {
		HandleCATCommand();
		return;
	}

	switch (UART_Command.Header.ID)
	{
		case 0x0514:
			CMD_0514(UART_Command.Buffer);
			break;
	
		case 0x051B:
			CMD_051B(UART_Command.Buffer);
			break;
	
		case 0x051D:
			CMD_051D(UART_Command.Buffer);
			break;
	
		case 0x051F:	// Not implementing non-authentic command
			break;
	
		case 0x0521:	// Not implementing non-authentic command
			break;
	
		case 0x0527:
			CMD_0527();
			break;
	
		case 0x0529:
			CMD_0529();
			break;
	
		case 0x052D:
			CMD_052D(UART_Command.Buffer);
			break;
	
		case 0x052F:
			CMD_052F(UART_Command.Buffer);
			break;
	
		case 0x05DD: // reset
			#if defined(ENABLE_OVERLAY)
				overlay_FLASH_RebootToBootloader();
			#else
				NVIC_SystemReset();
			#endif
			break;
			
#ifdef ENABLE_UART_RW_BK_REGS
		case 0x0601:
			CMD_0601_ReadBK4819Reg(UART_Command.Buffer);
			break;
		
		case 0x0602:
			CMD_0602_WriteBK4819Reg(UART_Command.Buffer);
			break;
#endif
	}
}
