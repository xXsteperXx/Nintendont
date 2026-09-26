/*

Nintendont (Kernel) - Playing Gamecubes in Wii mode on a Wii U

Copyright (C) 2013  crediar
Copyright (C) 2014 - 2019 FIX94

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation version 2.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

*/
#include "HID.h"
#include "Config.h"
#include "hidmem.h"
#include "usb.h"
#include "HID_controllers.h"

#include <stdlib.h>
#include "ff_utf8.h"

// v13: 2 USB controllers at the same time (Player 1 + Player 2)
// + XInput pads through /dev/usb/ven (GameSir Nova Lite dongle 3537:1040), SD only
// DS4 v2 (054C:09CC, interface 3) + 8BitDo Ultimate 2 dock (2DC8:6012)
extern int dbgprintf( const char *fmt, ...);

static u8 *kb_input = (u8*)0x13026C60;

#define GetDeviceChange 1
#define GetDeviceParameters 3
#define AttachFinish 6
#define ResumeDevice 16
#define ControlMessage 18
#define InterruptMessage 19

static const u8 ss_led_pattern[8] = {0x0, 0x02, 0x04, 0x08, 0x10, 0x12, 0x14, 0x18};

#define HID_STATUS 0x13003440
#define HID_CHANGE HID_STATUS+4
#define HID_CFG_SIZE HID_STATUS+8
#define HID_CFG_FILE 0x13003460

// memory for the 2nd controller (read by PADReadGC.c)
#define HID_CTRL2_ADDR		0x13005200
#define HID_PACKET2_ADDR	0x13005300
#define HID_STATUS2			0x13005380

#define HID_MAX_SLOTS	2
#define HID_PACKET_BUF	128
#define TMS()	(read32(HW_TIMER) / 1898)	// milliseconds, for the log

// "companion": the extra HID interface of the GameSir dongle (not a player),
// polled like Windows does, only to keep the dongle happy and log its data
static u32 CompID = 0, CompLen = 0, CompPending = 0, CompReads = 0, CompErrors = 0;
static vu32 compdone = 0;
static volatile s32 CompRet = 0;
static struct ipcmessage *compmsg = NULL;
static u8 *CompBuf = NULL;
struct _usb_msg comp_irq_req ALIGNED(32);

typedef void (*SlotReadFunc)(u32 idx);

typedef struct
{
	u32 Active;
	u32 DeviceID;
	u32 VID;
	u32 PID;
	u32 Iface;		// wIndex for control requests (3 on DS4 v2, 0 on others)
	u32 IsDS4;
	u32 LedSet;
	u32 EpIn;
	u32 EpOut;
	u32 MaxPacket;
	u32 MemPacketSize;
	u32 ReadPending;
	vu32 ReadDone;
	volatile s32 ReadRet;
	u32 Reads;
	u32 IsVen;			// XInput pad read through /dev/usb/ven
	u32 VenResubmit;
	u32 VenTimer;
	u32 VenErrors;
	SlotReadFunc Read;
	u8 *Packet;			// buffer used by IOS
	controller *Ctrl;	// config read by PADReadGC
	u8 *Out;			// packet read by PADReadGC
	struct ipcmessage *msg;
} hid_slot;

struct _usb_msg_a { struct _usb_msg m; } ALIGNED(32);

static hid_slot Slots[HID_MAX_SLOTS];
static struct _usb_msg_a SlotReadCtrl[HID_MAX_SLOTS] ALIGNED(32);
static struct _usb_msg_a SlotReadIrq[HID_MAX_SLOTS] ALIGNED(32);
struct _usb_msg sync_ctrl_req ALIGNED(32);
struct _usb_msg sync_irq_req ALIGNED(32);
struct _usb_msg ds4_sync_req ALIGNED(32);

static s32 HIDHandle = -1;
static u32 KeyboardID  = 0;
static u32 KBPending = 0;
static u32 bEndpointAddressKeyboard = 0;

static s32 RumbleSlot = -1;
static u32 RumbleType = 0;
static u32 RumbleEnabled = 0;
static u8 *RawRumbleDataOn = NULL;
static u8 *RawRumbleDataOff = NULL;
static u32 RawRumbleDataLen = 0;
static u32 RumbleTransferLen = 0;
static u32 RumbleTransfers = 0;

static const unsigned char rawData[] =
{
	0x01, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xFF, 0x27, 0x10, 0x00, 0x32, 
	0xFF, 0x27, 0x10, 0x00, 0x32, 0xFF, 0x27, 0x10, 0x00, 0x32, 0xFF, 0x27, 0x10, 0x00, 0x32, 0x00, 
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
	0x00,
};

struct _usb_msg read_kb_ctrl_req ALIGNED(32);
struct _usb_msg write_kb_ctrl_req ALIGNED(32);
struct _usb_msg read_kb_irq_req ALIGNED(32);
struct _usb_msg write_kb_irq_req ALIGNED(32);

static u8 *ps3buf = (u8*)NULL;
static u8 *gcbuf = (u8*)NULL;
static u8 *kbbuf = (u8*)NULL;
static u8 *DS4Big = NULL;
static u8 *DS4Feat = NULL;

RumbleFunc HIDRumble = NULL;

static usb_device_entry AttachedDevices[32] ALIGNED(32);

static struct ipcmessage *hidreadkeyboardmsg = NULL, *hidchangemsg = NULL, *hidattachmsg = NULL;
static u32 HID_Thread = 0;
static u32 HID_Timer = 0;
static u8 *hidheap = NULL;
static s32 hidqueue = -1;
static vu32 keyboardread = 0, hidchange = 0, hidattach = 0, hidattached = 0, hidwaittimer = 0;
static u32 HIDAlarm();
static s32 HIDInterruptMessage(hid_slot *s, u8 *Data, u32 Length, u32 Endpoint, s32 asyncqueue, struct ipcmessage *asyncmsg);
static s32 HIDControlMessage(hid_slot *s, u8 *Data, u32 Length, u32 RequestType, u32 Request, u32 Value, s32 asyncqueue, struct ipcmessage *asyncmsg);
static void SlotIRQRead(u32 idx);
static void SlotPS3Read(u32 idx);
static void SlotSubmitRead(u32 idx);
static void SlotVenRead(u32 idx);
static void PublishStatus(void);
static void VenUpdate(u32 LoaderRequest);
static void VenClose(void);
extern char __hid_stack_addr, __hid_stack_size;

void HIDInit( void )
{
	HIDHandle = IOS_Open("/dev/usb/hid", 0 );
	if(HIDHandle < 0) return; //should never happen

	ps3buf = (u8*)malloca( 64, 32 );
	gcbuf = (u8*)malloca( 32,32 );
	kbbuf = (u8*)malloca( 32,32 );
	DS4Big = (u8*)malloca( 544, 32 );
	DS4Feat = (u8*)malloca( 64, 32 );
	CompBuf = (u8*)malloca( 64, 32 );
	compmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);

	u32 i;
	memset32(Slots, 0, sizeof(Slots));
	for(i = 0; i < HID_MAX_SLOTS; ++i)
	{
		Slots[i].Packet = (u8*)malloca(HID_PACKET_BUF, 32);
		memset32(Slots[i].Packet, 0, HID_PACKET_BUF);
		Slots[i].msg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
	}
	Slots[0].Ctrl = (controller*)HID_CTRL;
	Slots[0].Out = (u8*)HID_Packet;
	Slots[1].Ctrl = (controller*)HID_CTRL2_ADDR;
	Slots[1].Out = (u8*)HID_PACKET2_ADDR;

	hidheap = (u8*)malloca(64,32);
	hidqueue = mqueue_create(hidheap, 16);
	hidreadkeyboardmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
	hidchangemsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
	hidattachmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
	HID_Thread = do_thread_create(HIDAlarm, ((u32*)&__hid_stack_addr), ((u32)(&__hid_stack_size)), 0x78);
	thread_continue(HID_Thread);

	hidattached = 0;
	hidwaittimer = 0;
	memset32(AttachedDevices, 0, sizeof(usb_device_entry)*32);
	IOS_IoctlAsync(HIDHandle, GetDeviceChange, NULL, 0, AttachedDevices, 0x180, hidqueue, hidchangemsg);

	memset32((void*)HID_STATUS, 0, 0x20);
	sync_after_write((void*)HID_STATUS, 0x20);
	memset32((void*)HID_CTRL2_ADDR, 0, 0x1A0);
	sync_after_write((void*)HID_CTRL2_ADDR, 0x1A0);

	mdelay(100);
	HID_Timer = read32(HW_TIMER);
}

// synchronous control request with a chosen interface (wIndex)
static s32 SlotCtrlSync(hid_slot *s, u16 iface, u8 reqtype, u8 req, u16 value, u16 len, u8 *data)
{
	struct _usb_msg *msg = &ds4_sync_req;
	u8 dir = !!(reqtype & USB_CTRLTYPE_DIR_DEVICE2HOST);
	memset32(msg, 0, sizeof(struct _usb_msg));
	msg->fd = s->DeviceID;
	msg->ctrl.bmRequestType = reqtype;
	msg->ctrl.bmRequest = req;
	msg->ctrl.wValue = value;
	msg->ctrl.wIndex = iface;
	msg->ctrl.wLength = len;
	msg->ctrl.rpData = data;
	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = data;
	msg->vec[1].len = len;
	sync_after_write(data, (len + 31) & ~31);
	s32 r = IOS_Ioctlv(HIDHandle, ControlMessage, 2-dir, dir, msg->vec);
	if(dir) sync_before_read(data, (len + 31) & ~31);
	return r;
}

// DS4 v2: without this the interrupt endpoint 0x81 never sends data
static void DS4WakeSequence(hid_slot *s)
{
	s32 r;
	//1. read HID report descriptor (standard request to interface 3)
	memset32(DS4Big, 0, 544);
	r = SlotCtrlSync(s, 3, 0x81, 0x06, 0x2200, 507, DS4Big);
	dbgprintf("DS4:getdesc ret=%d\r\n", r);
	//2. SET_IDLE 0
	r = SlotCtrlSync(s, 3, 0x21, 0x0A, 0x0000, 0, DS4Big);
	dbgprintf("DS4:setidle ret=%d\r\n", r);
	//3. feature 0xA3 (firmware info)
	memset32(DS4Big, 0, 64);
	r = SlotCtrlSync(s, 3, 0xA1, 0x01, 0x03A3, 49, DS4Big);
	dbgprintf("DS4:featA3 ret=%d\r\n", r);
	//4. output report 0x05: light bar
	memset32(DS4Big, 0, 64);
	DS4Big[0] = 0x05;
	DS4Big[1] = 0x02;
	if(s == &Slots[0])
		DS4Big[8] = 0x40;	//Player 1: blue
	else
		DS4Big[6] = 0x40;	//Player 2: red
	r = SlotCtrlSync(s, 3, 0x21, 0x09, 0x0205, 32, DS4Big);
	dbgprintf("DS4:led ret=%d\r\n", r);
	//5. SET_INTERFACE 3 alt 0 (standard, interface)
	r = SlotCtrlSync(s, 3, 0x01, 0x0B, 0x0000, 0, DS4Big);
	dbgprintf("DS4:setinterface ret=%d\r\n", r);
}

static void GenericWakeSequence(hid_slot *s)
{
	s32 r;
	memset32(DS4Big, 0, 544);
	r = SlotCtrlSync(s, 0, 0x81, 0x06, 0x2200, 256, DS4Big);
	dbgprintf("PAD:wake getdesc ret=%d\r\n", r);
	r = SlotCtrlSync(s, 0, 0x21, 0x0A, 0x0000, 0, DS4Big);
	dbgprintf("PAD:wake setidle ret=%d\r\n", r);
}

static void SlotGCInit(hid_slot *s)
{
	// Needed for some adapters clone
	HIDControlMessage(s, NULL, 0, USB_REQTYPE_INTERFACE_SET, USB_REQ_SETPROTOCOL, 1, 0, NULL);

	memset32(gcbuf, 0, 32);
	gcbuf[0] = 0x13;
	s32 ret = HIDInterruptMessage(s, gcbuf, 1, s->EpOut, 0, NULL);
	if( ret < 0 )
	{
		dbgprintf("HID:HIDGCInit:IOS_Ioctl( %u, %u, %u, %u, %u):%d\r\n", HIDHandle, 2, 32, 0, 0, ret );
		BootStatusError(-8, -7);
		mdelay(4000);
		Shutdown();
	}
}

static void SlotPS3Init(hid_slot *s)
{
	u8 *buf = (u8*)malloca( 0x20, 32 );
	memset32( buf, 0, 0x20 );
	s32 ret = HIDControlMessage(s, buf, 17, USB_REQTYPE_INTERFACE_GET,
			USB_REQ_GETREPORT, (USB_REPTYPE_FEATURE<<8) | 0xf2, 0, NULL);
	if( ret < 0 )
	{
		dbgprintf("HID:HIDPS3Init:IOS_Ioctl( %u, %u, %u, %u, %u):%d\r\n", HIDHandle, 2, 32, 0, 0, ret );
		BootStatusError(-8, -6);
		mdelay(4000);
		Shutdown();
	}
	free(buf);
}

static void SlotPS3SetLED(hid_slot *s, u8 led)
{
	ps3buf[10] = ss_led_pattern[led];
	sync_after_write(ps3buf, 64);

	s32 ret = HIDInterruptMessage(s, ps3buf, sizeof(rawData), 0x02, 0, NULL);
	if( ret < 0 ) 
		dbgprintf("ES:IOS_Ioctl():%d\r\n", ret );
}

static void SlotPS3SetRumble(hid_slot *s, u8 duration_right, u8 power_right, u8 duration_left, u8 power_left)
{
	ps3buf[3] = power_left;
	ps3buf[5] = power_right;
	sync_after_write(ps3buf, 64);

	s32 ret = HIDInterruptMessage(s, ps3buf, sizeof(rawData), 0x02, 0, NULL);
	if( ret < 0 )
		dbgprintf("ES:IOS_Ioctl():%d\r\n", ret );
}

static void SlotRelease(u32 idx)
{
	hid_slot *s = &Slots[idx];
	dbgprintf("HID:slot %u released (VID:%04X PID:%04X)\r\n", idx, s->VID, s->PID);
	s->Active = 0;
	s->DeviceID = 0;
	s->Read = NULL;
	s->IsVen = 0;
	s->VenResubmit = 0;
	if(RumbleSlot == (s32)idx)
	{
		RumbleSlot = -1;
		RumbleEnabled = 0;
		HIDRumble = NULL;
	}
}

/* ========================================================================== */
/*          XInput pads (GameSir Nova Lite dongle) through /dev/usb/ven        */
/* ========================================================================== */
// XInput pads use a vendor-class interface (FF/5D/01), IOS never shows it on
// /dev/usb/hid. With games on SD nobody else holds /dev/usb/ven in-game, so
// it is opened here. Based on the tested parts of Nintendont PR #1355.
// Transfers on ven are always async (a sync read on an idle pad never returns).

#define VEN_SHUTDOWN		2
#define VEN_ATTACH			4
#define VEN_CANCEL_ENDPOINT	17
#define VEN_POLL_TICKS		7600	// about 4ms between reads
#define VEN_REPORT_SIZE		20

static const char ven_path[] ALIGNED(32) = "/dev/usb/ven";
static s32 VenHandle = -1;
static u32 VenDisabled = 0, VenOpenTries = 0, VenOpenTimer = 0, VenWaitTimer = 0, VenLogged = 0;
static usb_device_entry VenDevices[32] ALIGNED(32);
static struct _usb_msg_a VenReadReq[HID_MAX_SLOTS] ALIGNED(32);
struct _usb_msg ven_write_req ALIGNED(32);
static struct ipcmessage *venchangemsg = NULL, *venattachmsg = NULL, *venoutmsg = NULL, *venctrlmsg = NULL;
static vu32 venchange = 0, venattach = 0, venoutbusy = 0, venctrlbusy = 0, venctrldone = 0;
static volatile s32 VenCtrlRet = 0;
static u8 *VenOutBuf = NULL, *VenCtrlBuf = NULL;
struct _usb_msg ven_ctrl_req ALIGNED(32);

// devices whose buttons only come through /dev/usb/ven
static const u16 VenOnlyIDs[][2] =
{
	{ 0x3537, 0x1040 },	// GameSir Nova Lite dongle, X mode
	{ 0x045E, 0x028E },	// wired Xbox 360 controller
};

static u32 IsVenOnly(u32 vid, u32 pid)
{
	u32 i;
	for(i = 0; i < sizeof(VenOnlyIDs) / sizeof(VenOnlyIDs[0]); ++i)
	{
		if(VenOnlyIDs[i][0] == vid && VenOnlyIDs[i][1] == pid)
			return 1;
	}
	return 0;
}

static s32 VenTransfer(hid_slot *s, u8 *Data, u32 Length, u32 Endpoint, struct ipcmessage *asyncmsg)
{
	u8 dir_in = !!(Endpoint & USB_ENDPOINT_IN);
	struct _usb_msg *msg = dir_in ? &VenReadReq[s - Slots].m : &ven_write_req;
	if(VenHandle < 0)
		return -1;
	memset32(msg, 0, sizeof(struct _usb_msg));
	msg->fd = s->DeviceID;
	msg->intr.rpData = Data;
	msg->intr.wLength = Length;
	msg->intr.bEndpoint = Endpoint;
	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = Data;
	msg->vec[1].len = Length;
	if(!dir_in)
		sync_after_write(Data, (Length + 31) & ~31);
	return IOS_IoctlvAsync(VenHandle, InterruptMessage, 2-dir_in, dir_in, msg->vec, hidqueue, asyncmsg);
}

static void PublishStatus(void)
{
	write32(HID_STATUS, Slots[0].Active ? 1 : 0);
	sync_after_write((void*)HID_STATUS, 0x20);
	write32(HID_STATUS2, Slots[1].Active ? 1 : 0);
	sync_after_write((void*)HID_STATUS2, 0x20);
}

// Loads the .ini / internal config of a new device into slot idx.
// Returns 1 if the slot is now in use.
static u32 SlotOpen(u32 idx, u32 LoaderRequest, u32 DeviceID, u32 DeviceVID, u32 DevicePID,
					u32 EpIn, u32 EpOut, u32 MaxPacket, u32 IsVen)
{
	hid_slot *s = &Slots[idx];
	controller *C = s->Ctrl;
	s32 ret;
	u32 i;

	s->Active = 0;
	s->DeviceID = DeviceID;
	s->VID = DeviceVID;
	s->PID = DevicePID;
	s->EpIn = EpIn;
	s->EpOut = EpOut;
	if(MaxPacket > HID_PACKET_BUF) MaxPacket = HID_PACKET_BUF;
	if(MaxPacket == 0) MaxPacket = 64;
	s->MaxPacket = MaxPacket;
	s->Iface = 0;
	s->IsDS4 = 0;
	s->LedSet = 0;
	s->Reads = 0;
	s->Read = NULL;
	s->IsVen = IsVen;
	s->VenResubmit = 0;
	s->VenErrors = 0;
	s->VenTimer = read32(HW_TIMER);

	u32 canRumble = (RumbleSlot < 0);
	u32 slotRumble = 0;
	RumbleFunc rfunc = NULL;

	dbgprintf("HID:v13 slot %u VID:%04X PID:%04X ep=%02X epout=%02X size=%u\r\n",
		idx, DeviceVID, DevicePID, EpIn, EpOut, MaxPacket);

	if(IsVen)
		canRumble = 0;
	else if( DeviceVID == 0x2dc8 )
		GenericWakeSequence(s);
	if( !IsVen && DeviceVID == 0x054c && DevicePID == 0x09cc )
	{
		s->IsDS4 = 1;
		s->Iface = 3;
		memset32(DS4Feat, 0, 64);
		ret = HIDControlMessage(s, DS4Feat, 37, USB_REQTYPE_INTERFACE_GET,
			USB_REQ_GETREPORT, (USB_REPTYPE_FEATURE<<8) | 0x02, 0, NULL);
		sync_before_read(DS4Feat, 64);
		dbgprintf("DS4:feat02 ret=%d\r\n", ret);
		DS4WakeSequence(s);
	}

	if( IsVen )
		; //nothing to wake up
	else if( DeviceVID == 0x054c && DevicePID == 0x0268 )
	{
		dbgprintf("HID:PS3 Dualshock Controller detected\r\n");
		memset32(ps3buf, 0, 64);
		memcpy(ps3buf, rawData, sizeof(rawData));
		SlotPS3Init(s);
		if(canRumble) slotRumble = 1;
		SlotPS3SetRumble(s, 0, 0, 0, 0);
	}
	else if( DeviceVID == 0x057e && DevicePID == 0x0337 )
		SlotGCInit(s);

	//Load controller config
	char *Data = NULL;
	if(LoaderRequest)
	{
		dbgprintf("Sending controller.ini request\r\n");
		memset32((void*)HID_STATUS, 0, 0x20);
		write32(HID_CHANGE, DeviceVID);
		write32(HID_CFG_SIZE, DevicePID);
		sync_after_write((void*)HID_STATUS, 0x20);
		while(1)
		{
			sync_before_read((void*)HID_STATUS, 0x20);
			if(read32(HID_CHANGE) == 0) break;
			mdelay(10);
		}
		u32 cfgsize = read32(HID_CFG_SIZE);
		if(cfgsize == 0)
			dbgprintf("HID:No controller config found!\r\n");
		else
		{
			Data = malloc(cfgsize+1);
			if(Data)
			{
				sync_before_read((void*)HID_CFG_FILE, cfgsize);
				memcpy(Data, (void*)HID_CFG_FILE, cfgsize);
				Data[cfgsize] = 0x00;	//null terminate the file
			}
		}
	}
	else
	{
		FIL f;
		u32 read;
		char directory[28];
		_sprintf(directory, "/controllers/%04X_%04X.ini", DeviceVID, DevicePID);
		dbgprintf("Preferred controller.ini file: %s\r\n", directory);

		ret = f_open_char( &f, directory, FA_OPEN_EXISTING|FA_READ);
		if(ret != FR_OK)
			ret = f_open_char( &f, "/controller.ini", FA_OPEN_EXISTING|FA_READ);
		else
			dbgprintf("%s was used\r\n", directory);
		if(ret != FR_OK)
			ret = f_open_char(&f, "/controller.ini.ini", FA_OPEN_EXISTING | FA_READ); // too many people don't read the instructions for windows
		if(ret != FR_OK)
			dbgprintf("HID:Failed to open config file:%u\r\n", ret );
		else
		{
			Data = (char*)malloc( f.obj.objsize + 1 );
			if(Data)
			{
				f_read( &f, Data, f.obj.objsize, &read );
				Data[f.obj.objsize] = 0x00;	//null terminate the file
			}
			f_close(&f);
		}
	}
	if(Data != NULL) //initial check
	{
		C->VID = ConfigGetValue( Data, "VID", 0 );
		C->PID = ConfigGetValue( Data, "PID", 0 );

		if( DeviceVID != C->VID || DevicePID != C->PID )
		{
			dbgprintf("HID:Config does not match device VID/PID\r\n");
			dbgprintf("HID:Config VID:%04X PID:%04X\r\n", C->VID, C->PID );
			free(Data);
			Data = NULL;
		}
	}
	if(Data == NULL)
	{
		controller *c = NULL;
		for(i = 0; i < sizeof(DefControllers) / sizeof(controller); ++i)
		{
			if(DefControllers[i].VID == DeviceVID && DefControllers[i].PID == DevicePID)
			{
				c = &DefControllers[i];
				dbgprintf("HID:Using Internal Controller Settings\r\n");
				break;
			}
		}
		if(c == NULL)
		{
			dbgprintf("HID:No Configs Found!\r\n");
			s->DeviceID = 0;
			return 0;
		}
		memcpy(C, c, sizeof(controller));
		if(canRumble)
		{
			for(i = 0; i < sizeof(DefRumble) / sizeof(rumble); ++i)
			{
				if(DefRumble[i].VID == DeviceVID && DefRumble[i].PID == DevicePID)
				{
					RawRumbleDataLen = DefRumble[i].RumbleDataLen;
					if(RawRumbleDataLen > 0)
					{
						dbgprintf("HID:Using Internal Rumble Settings\r\n");
						slotRumble = 1;
						u32 DataAligned = (RawRumbleDataLen+31) & (~31);

						if(RawRumbleDataOn != NULL) free(RawRumbleDataOn);
						RawRumbleDataOn = (u8*)malloca(DataAligned, 32);
						memset32(RawRumbleDataOn, 0, DataAligned);
						memcpy(RawRumbleDataOn, DefRumble[i].RumbleDataOn, RawRumbleDataLen);

						if(RawRumbleDataOff != NULL) free(RawRumbleDataOff);
						RawRumbleDataOff = (u8*)malloca(DataAligned, 32);
						memset32(RawRumbleDataOff, 0, DataAligned);
						memcpy(RawRumbleDataOff, DefRumble[i].RumbleDataOff, RawRumbleDataLen);

						RumbleType = DefRumble[i].RumbleType;
						RumbleTransferLen = DefRumble[i].RumbleTransferLen;
						RumbleTransfers = DefRumble[i].RumbleTransfers;
					}
					break;
				}
			}
		}
	}
	else
	{
		C->DPAD		= ConfigGetValue( Data, "DPAD", 0 );
		C->DigitalLR	= ConfigGetValue( Data, "DigitalLR", 0 );
		C->Polltype	= ConfigGetValue( Data, "Polltype", 0 );
		C->MultiIn	= ConfigGetValue( Data, "MultiIn", 0 );
		C->MultiInValue = 0;

		if( C->MultiIn )
		{
			C->MultiInValue= ConfigGetValue( Data, "MultiInValue", 0 );

			dbgprintf("HID:MultIn:%u\r\n", C->MultiIn );
			dbgprintf("HID:MultiInValue:%u\r\n", C->MultiInValue );
		}

		if( C->DPAD > 1 )
		{
			dbgprintf("HID: %u is an invalid DPAD value\r\n", C->DPAD );
			free(Data);
			s->DeviceID = 0;
			return 0;
		}

		C->Power.Offset	= ConfigGetValue( Data, "Power", 0 );
		C->Power.Mask	= ConfigGetValue( Data, "Power", 1 );

		C->A.Offset	= ConfigGetValue( Data, "A", 0 );
		C->A.Mask	= ConfigGetValue( Data, "A", 1 );

		C->B.Offset	= ConfigGetValue( Data, "B", 0 );
		C->B.Mask	= ConfigGetValue( Data, "B", 1 );

		C->X.Offset	= ConfigGetValue( Data, "X", 0 );
		C->X.Mask	= ConfigGetValue( Data, "X", 1 );

		C->Y.Offset	= ConfigGetValue( Data, "Y", 0 );
		C->Y.Mask	= ConfigGetValue( Data, "Y", 1 );

		C->ZL.Offset	= ConfigGetValue( Data, "ZL", 0 );
		C->ZL.Mask	= ConfigGetValue( Data, "ZL", 1 );

		C->Z.Offset	= ConfigGetValue( Data, "Z", 0 );
		C->Z.Mask	= ConfigGetValue( Data, "Z", 1 );

		C->L.Offset	= ConfigGetValue( Data, "L", 0 );
		C->L.Mask	= ConfigGetValue( Data, "L", 1 );

		C->R.Offset	= ConfigGetValue( Data, "R", 0 );
		C->R.Mask	= ConfigGetValue( Data, "R", 1 );

		C->S.Offset	= ConfigGetValue( Data, "S", 0 );
		C->S.Mask	= ConfigGetValue( Data, "S", 1 );

		C->Left.Offset	= ConfigGetValue( Data, "Left", 0 );
		C->Left.Mask		= ConfigGetValue( Data, "Left", 1 );

		C->Down.Offset	= ConfigGetValue( Data, "Down", 0 );
		C->Down.Mask		= ConfigGetValue( Data, "Down", 1 );

		C->Right.Offset	= ConfigGetValue( Data, "Right", 0 );
		C->Right.Mask	= ConfigGetValue( Data, "Right", 1 );

		C->Up.Offset		= ConfigGetValue( Data, "Up", 0 );
		C->Up.Mask		= ConfigGetValue( Data, "Up", 1 );

		if( C->DPAD )
		{
			C->RightUp.Offset	= ConfigGetValue( Data, "RightUp", 0 );
			C->RightUp.Mask		= ConfigGetValue( Data, "RightUp", 1 );

			C->DownRight.Offset	= ConfigGetValue( Data, "DownRight", 0 );
			C->DownRight.Mask	= ConfigGetValue( Data, "DownRight", 1 );

			C->DownLeft.Offset	= ConfigGetValue( Data, "DownLeft", 0 );
			C->DownLeft.Mask		= ConfigGetValue( Data, "DownLeft", 1 );

			C->UpLeft.Offset		= ConfigGetValue( Data, "UpLeft", 0 );
			C->UpLeft.Mask		= ConfigGetValue( Data, "UpLeft", 1 );
		}

		if( C->DPAD  &&	//DPAD == 1 and all offsets the same
			C->Left.Offset == C->Down.Offset &&
			C->Left.Offset == C->Right.Offset &&
			C->Left.Offset == C->Up.Offset &&
			C->Left.Offset == C->RightUp.Offset &&
			C->Left.Offset == C->DownRight.Offset &&
			C->Left.Offset == C->DownLeft.Offset &&
			C->Left.Offset == C->UpLeft.Offset )
		{
			C->DPADMask = C->Left.Mask | C->Down.Mask | C->Right.Mask | C->Up.Mask
				| C->RightUp.Mask | C->DownRight.Mask | C->DownLeft.Mask | C->UpLeft.Mask;	//mask is all the used bits ored togather
			if ((C->DPADMask & 0xF0) == 0)	//if hi nibble isnt used
				C->DPADMask = 0x0F;			//use all bits in low nibble
			if ((C->DPADMask & 0x0F) == 0)	//if low nibble isnt used
				C->DPADMask = 0xF0;			//use all bits in hi nibble
		}
		else
			C->DPADMask = 0xFFFF;	//check all the bits

		C->StickX.Offset		= ConfigGetValue( Data, "StickX", 0 );
		C->StickX.DeadZone	= ConfigGetValue( Data, "StickX", 1 );
		C->StickX.Radius		= ConfigGetDecValue( Data, "StickX", 2 );
		if (C->StickX.Radius == 0)
			C->StickX.Radius = 80;
		C->StickX.Radius = (u64)C->StickX.Radius * 1280 / (128 - C->StickX.DeadZone);	//adjust for DeadZone

		C->StickY.Offset		= ConfigGetValue( Data, "StickY", 0 );
		C->StickY.DeadZone	= ConfigGetValue( Data, "StickY", 1 );
		C->StickY.Radius		= ConfigGetDecValue( Data, "StickY", 2 );
		if (C->StickY.Radius == 0)
			C->StickY.Radius = 80;
		C->StickY.Radius = (u64)C->StickY.Radius * 1280 / (128 - C->StickY.DeadZone);	//adjust for DeadZone

		C->CStickX.Offset	= ConfigGetValue( Data, "CStickX", 0 );
		C->CStickX.DeadZone	= ConfigGetValue( Data, "CStickX", 1 );
		C->CStickX.Radius	= ConfigGetDecValue( Data, "CStickX", 2 );
		if (C->CStickX.Radius == 0)
			C->CStickX.Radius = 80;
		C->CStickX.Radius = (u64)C->CStickX.Radius * 1280 / (128 - C->CStickX.DeadZone);	//adjust for DeadZone

		C->CStickY.Offset	= ConfigGetValue( Data, "CStickY", 0 );
		C->CStickY.DeadZone	= ConfigGetValue( Data, "CStickY", 1 );
		C->CStickY.Radius	= ConfigGetDecValue( Data, "CStickY", 2 );
		if (C->CStickY.Radius == 0)
			C->CStickY.Radius = 80;
		C->CStickY.Radius = (u64)C->CStickY.Radius * 1280 / (128 - C->CStickY.DeadZone);	//adjust for DeadZone

		C->LAnalog	= ConfigGetValue( Data, "LAnalog", 0 );
		C->RAnalog	= ConfigGetValue( Data, "RAnalog", 0 );

		if(canRumble && ConfigGetValue( Data, "Rumble", 0 ))
		{
			RawRumbleDataLen = ConfigGetValue( Data, "RumbleDataLen", 0 );
			if(RawRumbleDataLen > 0)
			{
				slotRumble = 1;
				u32 DataAligned = (RawRumbleDataLen+31) & (~31);

				if(RawRumbleDataOn != NULL) free(RawRumbleDataOn);
				RawRumbleDataOn = (u8*)malloca(DataAligned, 32);
				memset32(RawRumbleDataOn, 0, DataAligned);
				ConfigGetValue( Data, "RumbleDataOn", 3 );

				if(RawRumbleDataOff != NULL) free(RawRumbleDataOff);
				RawRumbleDataOff = (u8*)malloca(DataAligned, 32);
				memset32(RawRumbleDataOff, 0, DataAligned);
				ConfigGetValue( Data, "RumbleDataOff", 4 );

				RumbleType = ConfigGetValue( Data, "RumbleType", 0 );
				RumbleTransferLen = ConfigGetValue( Data, "RumbleTransferLen", 0 );
				RumbleTransfers = ConfigGetValue( Data, "RumbleTransfers", 0 );
			}
		}
		free(Data);

		dbgprintf("HID:Config file for VID:%04X PID:%04X loaded\r\n", C->VID, C->PID );
	}

	if( C->Polltype == 0 )
		s->MemPacketSize = 128;
	else if (C->MultiIn == 4)
		s->MemPacketSize = 128;
	else
		s->MemPacketSize = s->MaxPacket;

	//make the config visible for PADReadGC
	sync_after_write(C, sizeof(controller));

	memset32(s->Out, 0, HID_PACKET_BUF);
	if(IsVen) //centered sticks until the first report arrives
	{
		s->Out[6] = s->Out[8] = 128;
		s->Out[7] = s->Out[9] = 127;
	}
	sync_after_write(s->Out, HID_PACKET_BUF);

	if(IsVen)
	{
		s->Read = SlotVenRead;
		s->MemPacketSize = s->MaxPacket;
	}
	else if(C->Polltype || s->IsDS4)
		s->Read = SlotIRQRead;
	else
		s->Read = SlotPS3Read;

	if((C->VID == 0x057E) && (C->PID == 0x0337))
	{
		rfunc = HIDGCRumble;
		slotRumble = canRumble;
	}
	else if(slotRumble)
	{
		if(C->Polltype)
		{
			if(RumbleType)
				rfunc = HIDIRQRumble;
			else
				rfunc = HIDCTRLRumble;
		}
		else
			rfunc = HIDPS3Rumble;
	}
	if(s->IsDS4 || IsVen) //DS4 v2 has no OUT endpoint here, XInput rumble not done
		slotRumble = 0;

	if(slotRumble && canRumble)
	{
		RumbleSlot = idx;
		RumbleEnabled = 1;
		HIDRumble = rfunc;
	}

	s->Active = 1;
	dbgprintf("HID:slot %u ready, Player %u\r\n", idx, idx+1);
	return 1;
}

static void CompSubmit(void)
{
	struct _usb_msg *msg = &comp_irq_req;
	memset32(msg, 0, sizeof(struct _usb_msg));
	msg->fd = CompID;
	msg->hid_intr_dir = 0; //IN
	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = CompBuf;
	msg->vec[1].len = CompLen;
	CompPending = 1;
	if(IOS_IoctlvAsync(HIDHandle, InterruptMessage, 1, 1, msg->vec, hidqueue, compmsg) < 0)
		CompPending = 0;
}

static void CompOpen(u32 DeviceID, u32 Iface, u32 MaxPacket)
{
	hid_slot tmp;
	s32 r;
	memset32(&tmp, 0, sizeof(tmp));
	tmp.DeviceID = DeviceID;
	dbgprintf("COMP:open t=%u id=%u iface=%u size=%u\r\n", TMS(), DeviceID, Iface, MaxPacket);
	//like Windows: read the report descriptor and set idle
	memset32(DS4Big, 0, 544);
	r = SlotCtrlSync(&tmp, Iface, 0x81, 0x06, 0x2200, 64, DS4Big);
	dbgprintf("COMP:desc ret=%d %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X\r\n", r,
		DS4Big[0], DS4Big[1], DS4Big[2], DS4Big[3], DS4Big[4], DS4Big[5],
		DS4Big[6], DS4Big[7], DS4Big[8], DS4Big[9], DS4Big[10], DS4Big[11]);
	r = SlotCtrlSync(&tmp, Iface, 0x21, 0x0A, 0x0000, 0, DS4Big);
	dbgprintf("COMP:setidle ret=%d\r\n", r);
	CompID = DeviceID;
	CompLen = (MaxPacket == 0 || MaxPacket > 64) ? 64 : MaxPacket;
	CompReads = 0;
	CompErrors = 0;
	if(!CompPending)
		CompSubmit();
}

static void CompRead(void)
{
	CompPending = 0;
	sync_before_read(CompBuf, 64);
	CompReads++;
	if(CompReads <= 10)
		dbgprintf("COMP:read t=%u n=%u ret=%d %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X\r\n",
			TMS(), CompReads, CompRet, CompBuf[0], CompBuf[1], CompBuf[2], CompBuf[3], CompBuf[4],
			CompBuf[5], CompBuf[6], CompBuf[7], CompBuf[8], CompBuf[9], CompBuf[10], CompBuf[11]);
	if(CompRet < 0)
	{
		if(++CompErrors > 50)
			CompID = 0;
	}
	else
		CompErrors = 0;
	if(CompID)
		CompSubmit();
}

s32 HIDOpen( u32 LoaderRequest )
{
	u32 i, j;
	dbgprintf("HIDOpen() t=%u\r\n", TMS());

	memset32((void*)HID_STATUS, 0, 0x20);
	sync_after_write((void*)HID_STATUS, 0x20);
	write32(HID_STATUS2, 0);
	sync_after_write((void*)HID_STATUS2, 0x20);

	//1. free slots of devices that are gone
	u32 Present[HID_MAX_SLOTS];
	u32 KBPresent = 0, CompPresent = 0;
	for(j = 0; j < HID_MAX_SLOTS; ++j)
		Present[j] = 0;
	for(i = 0; i < 32; ++i)
	{
		if(AttachedDevices[i].vid == 0)
			continue;
		u32 id = AttachedDevices[i].device_id;
		for(j = 0; j < HID_MAX_SLOTS; ++j)
		{
			if(Slots[j].Active && !Slots[j].IsVen && Slots[j].DeviceID == id)
				Present[j] = 1;
		}
		if(KeyboardID != 0 && id == KeyboardID)
			KBPresent = 1;
		if(CompID != 0 && id == CompID)
			CompPresent = 1;
	}
	if(!CompPresent)
		CompID = 0;
	for(j = 0; j < HID_MAX_SLOTS; ++j)
	{
		if(Slots[j].Active && !Slots[j].IsVen && !Present[j])
			SlotRelease(j);
	}
	if(!KBPresent)
		KeyboardID = 0;

	//2. open new devices
	s32 *io_buffer = (s32*)malloca(0x20, 32);
	u8 *HIDHeap = (u8*)malloca(0x60,32);
	for(i = 0; i < 32; ++i)
	{
		if(AttachedDevices[i].vid == 0)
			continue;
		u32 DeviceID = AttachedDevices[i].device_id;
		u32 InUse = (KeyboardID != 0 && DeviceID == KeyboardID) || (CompID != 0 && DeviceID == CompID);
		for(j = 0; j < HID_MAX_SLOTS; ++j)
		{
			if(Slots[j].Active && !Slots[j].IsVen && Slots[j].DeviceID == DeviceID)
				InUse = 1;
		}
		if(InUse)
			continue;
		u32 VenOnlyDev = IsVenOnly(AttachedDevices[i].vid, AttachedDevices[i].pid);

		s32 FreeSlot = -1;
		for(j = 0; j < HID_MAX_SLOTS; ++j)
		{
			if(!Slots[j].Active)
			{
				FreeSlot = j;
				break;
			}
		}
		if(FreeSlot < 0 && KeyboardID != 0)
			break; //nothing left to open

		u32 DeviceVID = AttachedDevices[i].vid;
		u32 DevicePID = AttachedDevices[i].pid;

		dbgprintf("HID:DeviceID:%u\r\n", DeviceID );
		dbgprintf("HID:VID:%04X PID:%04X\r\n", DeviceVID, DevicePID );

		memset32(io_buffer, 0, 0x20);
		io_buffer[0] = DeviceID;
		io_buffer[2] = 1; //resume device
		IOS_Ioctl(HIDHandle, ResumeDevice, io_buffer, 0x20, NULL, 0);

		memset32(HIDHeap, 0, 0x60);

		memset32(io_buffer, 0, 0x20);
		io_buffer[0] = DeviceID;
		io_buffer[2] = 0;
		IOS_Ioctl(HIDHandle, GetDeviceParameters, io_buffer, 0x20, HIDHeap, 0x60);

		u32 Offset = 36;

		u32 DeviceDescLength    = *(vu8*)(HIDHeap+Offset);
		Offset += (DeviceDescLength+3)&(~3);

		u32 ConfigurationLength = *(vu8*)(HIDHeap+Offset);
		Offset += (ConfigurationLength+3)&(~3);

		u32 InterfaceDescLength = *(vu8*)(HIDHeap+Offset);
		u32 bInterfaceNumber = *(vu8*)(HIDHeap+Offset+2);

		u32 bInterfaceClass = *(vu8*)(HIDHeap+Offset+5);
		u32 bInterfaceSubClass = *(vu8*)(HIDHeap+Offset+6);
		u32 bInterfaceProtocol = *(vu8*)(HIDHeap+Offset+7);
		dbgprintf("HID:bInterfaceClass:%02X\r\n", bInterfaceClass );
		dbgprintf("HID:bInterfaceSubClass:%02X\r\n", bInterfaceSubClass );
		dbgprintf("HID:bInterfaceProtocol:%02X\r\n", bInterfaceProtocol );

		Offset += (InterfaceDescLength+3)&(~3);

		u32 EndpointDescLengthO = *(vu8*)(HIDHeap+Offset);

		u32 bEndpointAddress = *(vu8*)(HIDHeap+Offset+2);
		u32 bEndpointAddressOut = 0;

		if( (bEndpointAddress & 0xF0) != 0x80 )
		{
			bEndpointAddressOut = bEndpointAddress;
			Offset += (EndpointDescLengthO+3)&(~3);
		}
		bEndpointAddress = *(vu8*)(HIDHeap+Offset+2);
		u32 wMaxPacketSize = *(vu16*)(HIDHeap+Offset+4);

		dbgprintf("HID:bEndpointAddress:%02X\r\n", bEndpointAddress );
		dbgprintf("HID:wMaxPacketSize  :%u\r\n", wMaxPacketSize );

		if(KeyboardID == 0 &&
			(bInterfaceClass == USB_CLASS_HID) &&
			(bInterfaceSubClass == USB_SUBCLASS_BOOT) &&
			(bInterfaceProtocol == USB_PROTOCOL_KEYBOARD))
		{
			dbgprintf("HID:Keyboard detected\r\n");
			memset32(&read_kb_ctrl_req, 0, sizeof(struct _usb_msg));
			memset32(&write_kb_ctrl_req, 0, sizeof(struct _usb_msg));
			memset32(&write_kb_irq_req, 0, sizeof(struct _usb_msg));
			KeyboardID = DeviceID;
			bEndpointAddressKeyboard = bEndpointAddress;
			//set to boot protocol (0)
			HIDControlMessage(NULL, NULL, 0, USB_REQTYPE_INTERFACE_SET, USB_REQ_SETPROTOCOL, 0, 0, NULL);
		}
		else if(VenOnlyDev)
		{
			//its buttons come through /dev/usb/ven, only keep this interface busy
			if(CompID == 0 && bInterfaceProtocol != USB_PROTOCOL_MOUSE)
				CompOpen(DeviceID, bInterfaceNumber, wMaxPacketSize);
		}
		else if(FreeSlot >= 0 &&
			(bInterfaceProtocol != USB_PROTOCOL_KEYBOARD) &&
			(bInterfaceProtocol != USB_PROTOCOL_MOUSE))
		{
			//a composite device (DS4 v2) must not take the 2nd slot with a non-HID interface
			u32 Extra = 0;
			if(bInterfaceClass != USB_CLASS_HID)
			{
				for(j = 0; j < HID_MAX_SLOTS; ++j)
				{
					if(Slots[j].Active && Slots[j].VID == DeviceVID && Slots[j].PID == DevicePID)
						Extra = 1;
				}
			}
			if(Extra)
				dbgprintf("HID:extra interface of an open device, skipped\r\n");
			else
				SlotOpen(FreeSlot, LoaderRequest, DeviceID, DeviceVID, DevicePID,
					bEndpointAddress, bEndpointAddressOut, wMaxPacketSize, 0);
		}
	}
	free(io_buffer);
	free(HIDHeap);

	//3. (re)start reading, only where no read is waiting already
	for(j = 0; j < HID_MAX_SLOTS; ++j)
	{
		if(Slots[j].Active && !Slots[j].ReadPending)
			SlotSubmitRead(j);
	}

	memset32((void*)HID_STATUS, 0, 0x20);
	if(!Slots[0].Active)
		dbgprintf("HID:No controller in slot 0\r\n");
	PublishStatus();

	if( KeyboardID == 0 )
	{
		dbgprintf("HID:No keyboard connected!\r\n");
		memset(kb_input, 0, 8);
		sync_after_write(kb_input, 0x20);
	}
	else if(!KBPending) //(re)start reading
	{
		KBPending = 1;
		if(HIDInterruptMessage(NULL, kbbuf, 8, bEndpointAddressKeyboard, hidqueue, hidreadkeyboardmsg) < 0)
			KBPending = 0;
	}

	return 0;
}

void HIDClose()
{
	VenClose();
	IOS_Close(HIDHandle);
	HIDHandle = -1;
}

static u32 HIDAlarm()
{
	struct ipcmessage *msg = NULL;
	u32 i, slot;
	while(1)
	{
		mqueue_recv(hidqueue, &msg, 0);
		slot = 0;
		for(i = 0; i < HID_MAX_SLOTS; ++i)
		{
			if(msg == Slots[i].msg)
			{
				Slots[i].ReadRet = (s32)msg->result;
				slot = i+1;
			}
		}
		if(msg == venctrlmsg)
			VenCtrlRet = (s32)msg->result;
		if(msg == compmsg)
			CompRet = (s32)msg->result;
		mqueue_ack(msg, 0);
		if(slot)
			Slots[slot-1].ReadDone = 1;
		else if(msg == compmsg)
			compdone = 1;
		else if(msg == venctrlmsg)
		{
			venctrlbusy = 0;
			venctrldone = 1;
		}
		else if(msg == venoutmsg)
			venoutbusy = 0;
		else if(msg == venchangemsg)
			venchange = 1;
		else if(msg == venattachmsg)
			venattach = 1;
		else if(msg == hidreadkeyboardmsg)
			keyboardread = 1;
		else if(msg == hidchangemsg)
			hidchange = 1;
		else
			hidattach = 1;
	}
	return 0;
}

// s == NULL means keyboard
static s32 HIDControlMessage(hid_slot *s, u8 *Data, u32 Length, u32 RequestType, u32 Request, u32 Value, s32 asyncqueue, struct ipcmessage *asyncmsg)
{
	u8 request_dir = !!(RequestType & USB_CTRLTYPE_DIR_DEVICE2HOST);

	struct _usb_msg *msg;
	if(s == NULL)
	{
		msg = request_dir ? &read_kb_ctrl_req : &write_kb_ctrl_req;
		memset32(msg, 0, sizeof(struct _usb_msg));
		msg->fd = KeyboardID;
		msg->ctrl.wIndex = 0;
	}
	else
	{
		if(asyncmsg != NULL)
			msg = &SlotReadCtrl[s - Slots].m;
		else
			msg = &sync_ctrl_req;
		memset32(msg, 0, sizeof(struct _usb_msg));
		msg->fd = s->DeviceID;
		msg->ctrl.wIndex = s->Iface;
	}

	msg->ctrl.bmRequestType = RequestType;
	msg->ctrl.bmRequest = Request;
	msg->ctrl.wValue = Value;
	msg->ctrl.wLength = Length;
	msg->ctrl.rpData = Data;

	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = Data;
	msg->vec[1].len = Length;

	if(asyncmsg != NULL)
		return IOS_IoctlvAsync(HIDHandle, ControlMessage, 2-request_dir, request_dir, msg->vec, asyncqueue, asyncmsg);
	return IOS_Ioctlv(HIDHandle, ControlMessage, 2-request_dir, request_dir, msg->vec);
}

// s == NULL means keyboard
static s32 HIDInterruptMessage(hid_slot *s, u8 *Data, u32 Length, u32 Endpoint, s32 asyncqueue, struct ipcmessage *asyncmsg)
{
	u8 endpoint_dir = !!(Endpoint & USB_ENDPOINT_IN);

	struct _usb_msg *msg;
	if(s == NULL)
	{
		msg = endpoint_dir ? &read_kb_irq_req : &write_kb_irq_req;
		memset32(msg, 0, sizeof(struct _usb_msg));
		msg->fd = KeyboardID;
	}
	else
	{
		if(asyncmsg != NULL)
			msg = &SlotReadIrq[s - Slots].m;
		else
			msg = &sync_irq_req;
		memset32(msg, 0, sizeof(struct _usb_msg));
		msg->fd = s->DeviceID;
	}
	msg->hid_intr_dir = !endpoint_dir;

	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = Data;
	msg->vec[1].len = Length;

	if(asyncmsg != NULL)
		return IOS_IoctlvAsync(HIDHandle, InterruptMessage, 2-endpoint_dir, endpoint_dir, msg->vec, asyncqueue, asyncmsg);
	return IOS_Ioctlv(HIDHandle, InterruptMessage, 2-endpoint_dir, endpoint_dir, msg->vec);
}

static void SlotSubmitRead(u32 idx)
{
	hid_slot *s = &Slots[idx];
	s32 r;
	s->ReadPending = 1;
	if(s->IsVen)
		r = VenTransfer(s, s->Packet, s->MaxPacket, s->EpIn, s->msg);
	else if(s->Read == SlotPS3Read)
		r = HIDControlMessage(s, s->Packet, SS_DATA_LEN, USB_REQTYPE_INTERFACE_GET,
			USB_REQ_GETREPORT, (USB_REPTYPE_INPUT<<8) | 0x1, hidqueue, s->msg);
	else
		r = HIDInterruptMessage(s, s->Packet, s->MaxPacket, s->EpIn, hidqueue, s->msg);
	if(r < 0)
	{
		s->ReadPending = 0;
		if(s->IsVen) //no callback will come, retry later
		{
			s->VenErrors++;
			s->VenResubmit = 1;
			s->VenTimer = read32(HW_TIMER);
		}
		if(s->Reads < 3)
			dbgprintf("HID:slot %u read submit failed %d\r\n", idx, r);
	}
}

static void SlotPS3Read(u32 idx)
{
	hid_slot *s = &Slots[idx];
	u8 *Packet = s->Packet;
	sync_before_read(Packet, HID_PACKET_BUF);
	if( !s->LedSet && Packet[4] )
	{
		SlotPS3SetLED(s, idx+1);
		s->LedSet = 1;
	}
	memcpy(s->Out, Packet, SS_DATA_LEN);
	sync_after_write(s->Out, SS_DATA_LEN);

	SlotSubmitRead(idx);
}

static void SlotIRQRead(u32 idx)
{
	hid_slot *s = &Slots[idx];
	controller *C = s->Ctrl;
	u8 *Packet = s->Packet;
	u32 len = s->MaxPacket;
	u8 controllerNumber;

	sync_before_read(Packet, HID_PACKET_BUF);
	s->Reads++;
	if(s->Reads <= 3)
		dbgprintf("HID:slot %u read n=%u ret=%d %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X\r\n",
			idx, s->Reads, s->ReadRet, Packet[0], Packet[1], Packet[2], Packet[3], Packet[4],
			Packet[5], Packet[6], Packet[7], Packet[8], Packet[9]);

	if(s->ReadRet < 0)	//error, keep the last good data
		goto dohidirqread;

	switch( C->MultiIn )
	{
		default:
		case 0:	// MultiIn disabled
		case 3: // multiple controllers from a single adapter all controllers in 1 message
			break;
		case 1:	// match single controller filter on the first byte
			if (Packet[0] != C->MultiInValue)
				goto dohidirqread;
			break;
		case 2: // multiple controllers from a single adapter first byte contains controller number
			if ((Packet[0] < C->MultiInValue) || (Packet[0] > NIN_CFG_MAXPAD))
				goto dohidirqread;
			break;
		case 4:	// Multiple controllers from a single adapter, under seperate packets, to be merged into a single HID_Packet.
			controllerNumber = Packet[0];

			// Unwanted packet => try again
			if ((controllerNumber < 1) || (controllerNumber > C->MultiInValue) || (controllerNumber > 4))
				goto dohidirqread;

			// Wanted packet => merge it in on its 32 byte boundary
			memcpy(s->Out + (32 * (controllerNumber-1)), Packet, (len > 32) ? 32 : len);

			// Final packet => sync all the packets
			if (controllerNumber == C->MultiInValue)
				sync_after_write(s->Out, 128);

			goto dohidirqread;
			break;
	}
	memcpy(s->Out, Packet, len);
	sync_after_write(s->Out, len);
dohidirqread:
	SlotSubmitRead(idx);
}

/* ---------------------- /dev/usb/ven (XInput) part ------------------------ */

static void VenRearm(void)
{
	memset32(VenDevices, 0, sizeof(usb_device_entry)*32);
	IOS_IoctlAsync(VenHandle, GetDeviceChange, NULL, 0, VenDevices, 0x180, hidqueue, venchangemsg);
}

static void VenSetLED(hid_slot *s, u32 idx)
{
	if(s->EpOut == 0 || VenOutBuf == NULL || venoutbusy)
		return;
	memset32(VenOutBuf, 0, 32);
	VenOutBuf[0] = 0x01;
	VenOutBuf[1] = 0x03;
	VenOutBuf[2] = 0x06 + idx;	// ring light: player 1 / player 2
	venoutbusy = 1;
	s32 r = VenTransfer(s, VenOutBuf, 3, s->EpOut, venoutmsg);
	if(r < 0)
		venoutbusy = 0;
	dbgprintf("VEN:led ret=%d\r\n", r);
}

static s32 VenCancelEndpoint(u32 DeviceID, u32 Endpoint)
{
	s32 ret;
	s32 *buf = (s32*)malloca(32, 32);
	memset32(buf, 0, 32);
	buf[0] = DeviceID;
	buf[2] = Endpoint;
	ret = IOS_Ioctl(VenHandle, VEN_CANCEL_ENDPOINT, buf, 32, NULL, 0);
	free(buf);
	return ret;
}

// Linux xpad: "Some third-party Xbox 360-style controllers require this
// message to finish initialization." Vendor IN request 0x01, wValue 0x0100,
// 20 bytes. Without it the GameSir dongle resets itself every few seconds.
static void VenMagic(u32 DeviceID, u32 Iface)
{
	struct _usb_msg *msg = &ven_ctrl_req;
	if(VenCtrlBuf == NULL || venctrlbusy)
		return;
	memset32(VenCtrlBuf, 0, 32);
	sync_after_write(VenCtrlBuf, 32);
	memset32(msg, 0, sizeof(struct _usb_msg));
	msg->fd = DeviceID;
	msg->ctrl.bmRequestType = 0xC1;	//device to host, vendor, interface
	msg->ctrl.bmRequest = 0x01;
	msg->ctrl.wValue = 0x0100;
	msg->ctrl.wIndex = Iface;
	msg->ctrl.wLength = 20;
	msg->ctrl.rpData = VenCtrlBuf;
	msg->vec[0].data = msg;
	msg->vec[0].len = 64;
	msg->vec[1].data = VenCtrlBuf;
	msg->vec[1].len = 20;
	venctrlbusy = 1;
	s32 r = IOS_IoctlvAsync(VenHandle, ControlMessage, 1, 1, msg->vec, hidqueue, venctrlmsg);
	if(r < 0)
		venctrlbusy = 0;
	dbgprintf("VEN:magic submit ret=%d\r\n", r);
}

static u32 VenOpen(void)
{
	u32 i, j, e, opened = 0;
	s32 r;
	s32 *io = (s32*)malloca(0x20, 32);
	u8 *Heap = (u8*)malloca(0xC0, 32);

	for(i = 0; i < 32; ++i)
	{
		u32 vid = VenDevices[i].vid;
		u32 pid = VenDevices[i].pid;
		if(vid == 0)
			continue;
		u32 id = VenDevices[i].device_id;
		if(VenLogged < 16)
		{
			VenLogged++;
			dbgprintf("VEN:device t=%u id=%u VID:%04X PID:%04X token:%08X\r\n", TMS(), id, vid, pid, VenDevices[i].token);
		}
		if(!IsVenOnly(vid, pid))
			continue;

		u32 InUse = 0;
		for(j = 0; j < HID_MAX_SLOTS; ++j)
		{
			if(Slots[j].Active && Slots[j].IsVen && Slots[j].DeviceID == id)
				InUse = 1;
		}
		if(InUse)
			continue;

		s32 FreeSlot = -1;
		for(j = 0; j < HID_MAX_SLOTS; ++j)
		{
			if(!Slots[j].Active)
			{
				FreeSlot = j;
				break;
			}
		}
		if(FreeSlot < 0)
		{
			dbgprintf("VEN:no free slot for %04X:%04X\r\n", vid, pid);
			break;
		}

		memset32(io, 0, 0x20);
		io[0] = id;
		r = IOS_Ioctl(VenHandle, VEN_ATTACH, io, 0x20, NULL, 0);
		dbgprintf("VEN:attach ret=%d\r\n", r);

		memset32(io, 0, 0x20);
		io[0] = id;
		io[2] = 1; //resume
		r = IOS_Ioctl(VenHandle, ResumeDevice, io, 0x20, NULL, 0);
		dbgprintf("VEN:resume ret=%d\r\n", r);

		memset32(Heap, 0, 0xC0);
		memset32(io, 0, 0x20);
		io[0] = id;
		io[2] = 0;
		r = IOS_Ioctl(VenHandle, GetDeviceParameters, io, 0x20, Heap, 0xC0);
		dbgprintf("VEN:params ret=%d\r\n", r);
		for(e = 20; e < 100; e += 16)
			dbgprintf("VEN:%02X: %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X\r\n", e,
				Heap[e], Heap[e+1], Heap[e+2], Heap[e+3], Heap[e+4], Heap[e+5], Heap[e+6], Heap[e+7],
				Heap[e+8], Heap[e+9], Heap[e+10], Heap[e+11], Heap[e+12], Heap[e+13], Heap[e+14], Heap[e+15]);
		if(r < 0)
			continue;

		// layout: device desc @20, config @40, interface @52, endpoints @64 + 8*n
		if(Heap[21] != USB_DT_DEVICE || Heap[53] != USB_DT_INTERFACE)
		{
			dbgprintf("VEN:unexpected descriptor layout\r\n");
			continue;
		}
		u32 nep = Heap[56];
		dbgprintf("VEN:interface %u class %02X/%02X/%02X endpoints %u\r\n",
			Heap[54], Heap[57], Heap[58], Heap[59], nep);
		if(Heap[57] != 0xFF || Heap[58] != 0x5D || Heap[59] != 0x01)
			continue; //not the XInput gamepad interface

		u32 EpIn = 0, EpOut = 0, Size = 0;
		for(e = 0; e < nep && e < 8; ++e)
		{
			u32 o = 64 + 8*e;
			if(Heap[o+1] != USB_DT_ENDPOINT)
				continue;
			u32 addr = Heap[o+2];
			u32 attr = Heap[o+3];
			u32 size = (Heap[o+4] << 8) | Heap[o+5];
			if((attr & 3) != USB_ENDPOINT_INTERRUPT)
				continue;
			if((addr & USB_ENDPOINT_IN) && !EpIn)
			{
				EpIn = addr;
				Size = size;
			}
			else if(!(addr & USB_ENDPOINT_IN) && !EpOut)
				EpOut = addr;
		}
		dbgprintf("VEN:ep in %02X out %02X size %u\r\n", EpIn, EpOut, Size);
		if(!EpIn || Size < VEN_REPORT_SIZE)
			continue;

		// no SET_CONFIGURATION (IOS already did it), just reset the endpoint state
		r = VenCancelEndpoint(id, EpIn);
		dbgprintf("VEN:cancel ret=%d\r\n", r);

		//start reading right away (like Linux), before the slow .ini load
		{
			hid_slot *vs = &Slots[FreeSlot];
			vs->DeviceID = id;
			vs->EpIn = EpIn;
			vs->EpOut = EpOut;
			vs->MaxPacket = (Size > HID_PACKET_BUF) ? HID_PACKET_BUF : Size;
			vs->IsVen = 1;
			vs->Reads = 0;
			if(!vs->ReadPending)
				SlotSubmitRead(FreeSlot);
		}
		VenMagic(id, Heap[54]);

		if(!SlotOpen(FreeSlot, 0, id, vid, pid, EpIn, EpOut, Size, 1))
			continue;

		PublishStatus();
		if(!Slots[FreeSlot].ReadPending)
			SlotSubmitRead(FreeSlot);
		VenSetLED(&Slots[FreeSlot], FreeSlot);
		opened = 1;
	}
	free(io);
	free(Heap);
	return opened;
}

static u8 VenAxis(s16 v)
{
	return (u8)(((s32)v + 32768) >> 8);
}

static void SlotVenRead(u32 idx)
{
	hid_slot *s = &Slots[idx];
	u8 *P = s->Packet;
	s32 ret = s->ReadRet;

	sync_before_read(P, HID_PACKET_BUF);
	s->Reads++;
	if(s->Reads <= 5 || (ret < 0 && s->VenErrors < 3))
		dbgprintf("VEN:t=%u slot %u read n=%u ret=%d %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X %02X\r\n",
			TMS(), idx, s->Reads, ret, P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7],
			P[8], P[9], P[10], P[11], P[12], P[13]);

	if(ret < 0)
	{
		if(++s->VenErrors > 200)
		{
			dbgprintf("VEN:slot %u too many errors, waiting for a replug\r\n", idx);
			SlotRelease(idx);
			PublishStatus();
			VenRearm();
			return;
		}
	}
	else if(ret >= VEN_REPORT_SIZE && P[0] == 0x00 && P[1] >= VEN_REPORT_SIZE)
	{
		u8 cooked[VEN_REPORT_SIZE];
		s16 lx = (s16)(P[6]  | (P[7]  << 8));
		s16 ly = (s16)(P[8]  | (P[9]  << 8));
		s16 rx = (s16)(P[10] | (P[11] << 8));
		s16 ry = (s16)(P[12] | (P[13] << 8));
		s->VenErrors = 0;
		// bytes 0-5 as sent (buttons, triggers), 6-9 sticks as 8 bit
		memcpy(cooked, P, VEN_REPORT_SIZE);
		cooked[6] = VenAxis(lx);
		cooked[7] = 255 - VenAxis(ly);
		cooked[8] = VenAxis(rx);
		cooked[9] = 255 - VenAxis(ry);
		memcpy(s->Out, cooked, VEN_REPORT_SIZE);
		sync_after_write(s->Out, 32);
	}
	// anything else is a status packet, keep the last report

	// next read is sent by VenUpdate, spaced a little
	s->VenResubmit = 1;
	s->VenTimer = read32(HW_TIMER);
}

static void VenUpdate(u32 LoaderRequest)
{
	u32 i;
	if(LoaderRequest || VenDisabled)
		return;	// the loader owns /dev/usb/ven while the menu runs

	if(VenHandle < 0)
	{
		if(VenOpenTries >= 10)
			return;
		if(VenOpenTries && TimerDiffTicks(VenOpenTimer) < 1900000)	// about 1 second
			return;
		VenOpenTimer = read32(HW_TIMER);
		VenOpenTries++;
		if(ConfigGetConfig(NIN_CFG_USB))
		{
			dbgprintf("VEN:games on USB, XInput pads disabled\r\n");
			VenDisabled = 1;
			return;
		}
		s32 fd = IOS_Open(ven_path, 0);
		dbgprintf("VEN:open try %u ret=%d\r\n", VenOpenTries, fd);
		if(fd < 0)
			return;
		VenHandle = fd;
		if(venchangemsg == NULL)
		{
			venchangemsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
			venattachmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
			venoutmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
			venctrlmsg = (struct ipcmessage*)malloca(sizeof(struct ipcmessage), 32);
			VenOutBuf = (u8*)malloca(32, 32);
			VenCtrlBuf = (u8*)malloca(32, 32);
		}
		VenRearm();
		return;
	}

	if(venchange)
	{
		venchange = 0;
		IOS_IoctlAsync(VenHandle, AttachFinish, NULL, 0, NULL, 0, hidqueue, venattachmsg);
	}
	if(venctrldone)
	{
		venctrldone = 0;
		sync_before_read(VenCtrlBuf, 32);
		dbgprintf("VEN:t=%u magic ret=%d %02X %02X %02X %02X %02X %02X %02X %02X\r\n", TMS(), VenCtrlRet,
			VenCtrlBuf[0], VenCtrlBuf[1], VenCtrlBuf[2], VenCtrlBuf[3],
			VenCtrlBuf[4], VenCtrlBuf[5], VenCtrlBuf[6], VenCtrlBuf[7]);
	}
	if(venattach)
	{
		if(VenWaitTimer < 10)	//answer the dongle quickly, it resets itself if nobody talks to it
			VenWaitTimer++;
		else
		{
			venattach = 0;
			VenWaitTimer = 0;
			if(!VenOpen())
				VenRearm();	//keep one request waiting for the next plug-in
		}
	}
	for(i = 0; i < HID_MAX_SLOTS; ++i)
	{
		hid_slot *s = &Slots[i];
		if(s->Active && s->IsVen && s->VenResubmit && !s->ReadPending &&
			TimerDiffTicks(s->VenTimer) > VEN_POLL_TICKS)
		{
			s->VenResubmit = 0;
			SlotSubmitRead(i);
		}
	}
}

static void VenClose(void)
{
	if(VenHandle >= 0)
	{
		IOS_Ioctl(VenHandle, VEN_SHUTDOWN, NULL, 0, NULL, 0);
		IOS_Close(VenHandle);
		VenHandle = -1;
	}
}

void HIDPS3Rumble( u32 Enable )
{
	if(RumbleSlot < 0) return;
	hid_slot *s = &Slots[RumbleSlot];
	switch( Enable )
	{
		case 0:	// stop
		case 2:	// hard stop
			SlotPS3SetRumble( s, 0, 0, 0, 0 );
		break;
		case 1: // start
			SlotPS3SetRumble( s, 0, 0xFF, 0, 1 );
		break;
	}
}

void HIDGCRumble(u32 input)
{
	if(RumbleSlot < 0) return;
	hid_slot *s = &Slots[RumbleSlot];
	gcbuf[0] = 0x11;
	gcbuf[1] = input & 1;
	gcbuf[2] = (input >> 1) & 1;
	gcbuf[3] = (input >> 2) & 1;
	gcbuf[4] = (input >> 3) & 1;

	HIDInterruptMessage(s, gcbuf, 5, s->EpOut, 0, NULL);
}

void HIDIRQRumble(u32 Enable)
{
	if(RumbleSlot < 0) return;
	hid_slot *s = &Slots[RumbleSlot];
	u8 *buf = (Enable == 1) ? RawRumbleDataOn : RawRumbleDataOff;
	u32 i = 0;
irqrumblerepeat:
	HIDInterruptMessage(s, buf, RumbleTransferLen, s->EpOut, 0, NULL);
	i++;
	if(i < RumbleTransfers)
	{
		buf += RumbleTransferLen;
		goto irqrumblerepeat;
	}
}

void HIDCTRLRumble(u32 Enable)
{
	if(RumbleSlot < 0) return;
	hid_slot *s = &Slots[RumbleSlot];
	u8 *buf = (Enable == 1) ? RawRumbleDataOn : RawRumbleDataOff;
	u32 i = 0;
ctrlrumblerepeat:
	i++;
	HIDControlMessage(s, buf, RumbleTransferLen, USB_REQTYPE_INTERFACE_SET,
			USB_REQ_SETREPORT, (USB_REPTYPE_OUTPUT<<8) | 0x1, 0, NULL);
	if(i < RumbleTransfers)
	{
		buf += RumbleTransferLen;
		goto ctrlrumblerepeat;
	}
}

u32 ConfigGetValue( char *Data, const char *EntryName, u32 Entry )
{
	char entryname[128];
	_sprintf( entryname, "\n%s=", EntryName );

	char *str = strstr( Data, entryname );
	if( str == (char*)NULL )
	{
		dbgprintf("Entry:\"%s\" not found!\r\n", EntryName );
		return 0;
	}

	str += strlen(entryname); // Skip '='

	char *strEnd = strchr( str, 0x0A );
	u32 ret = 0;
	u32 i;

	switch (Entry)
	{
		case 0:
			ret = strtoul(str, NULL, 16);
			break;

		case 1:
			str = strstr( str, "," );
			if( str == (char*)NULL || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip ,

			ret = strtoul(str, NULL, 16);
			break;

		case 2:
			str = strstr( str, "," );
			if( str == (char*)NULL || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip the first ,

			str = strstr( str, "," );
			if( str == (char*)NULL || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip the second ,

			ret = strtoul(str, NULL, 16);
			break;

		case 3:
			for(i = 0; i < RawRumbleDataLen; ++i)
			{
				RawRumbleDataOn[i] = strtoul(str, NULL, 16);
				str = strstr( str, "," )+1;
			}
			break;

		case 4:
			for(i = 0; i < RawRumbleDataLen; ++i)
			{
				RawRumbleDataOff[i] = strtoul(str, NULL, 16);
				str = strstr( str, "," )+1;
			}
			break;

		default:
			break;
	}

	return ret;
}

u32 ConfigGetDecValue( char *Data, const char *EntryName, u32 Entry )
{
	char entryname[128];
	_sprintf( entryname, "\n%s=", EntryName );

	char *str = strstr( Data, entryname );
	if( str == (char*)NULL )
	{
		dbgprintf("Entry:\"%s\" not found!\r\n", EntryName );
		return 0;
	}

	str += strlen(entryname); // Skip '='

	char *strEnd = strchr( str, 0x0A );
	u32 ret = 0;

	switch (Entry)
	{
		case 0:
			ret = strtoul(str, NULL, 10);
			break;

		case 1:
			str = strstr( str, "," );
			if( str == (char*)NULL || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip ,

			ret = strtoul(str, NULL, 10);
			break;

		case 2:
			str = strstr( str, "," );
			if( str == (char*)NULL  || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip the first ,

			str = strstr( str, "," );
			if( str == (char*)NULL  || str > strEnd )
			{
				dbgprintf("No \",\" found in entry.\r\n");
				break;
			}

			str++; //Skip the second ,

			ret = strtoul(str, NULL, 10);
			break;

		default:
			break;
	}

	return ret;
}

static void KeyboardRead()
{
	memcpy(kb_input, kbbuf, 8);
	sync_after_write(kb_input, 0x20);
	KBPending = 1;
	if(HIDInterruptMessage(NULL, kbbuf, 8, bEndpointAddressKeyboard, hidqueue, hidreadkeyboardmsg) < 0)
		KBPending = 0;
}

vu32 HIDRumbleCurrent = 0, HIDRumbleLast = 0;
vu32 MotorCommand = 0x13003020;
void HIDUpdateRegisters(u32 LoaderRequest)
{
	u32 i;
	if(TimerDiffTicks(HID_Timer) > 3800)	// about 500 times a second
	{
		if(hidchange == 1)
		{
			hidattached = 0;
			//wait half a second for devices to
			//actually attach properly
			if(hidwaittimer < 120)
				hidwaittimer++;
			else
			{
				hidchange = 0;
				hidwaittimer = 0;
				//If you dont do that it wont update anymore
				IOS_IoctlAsync(HIDHandle, AttachFinish, NULL, 0, NULL, 0, hidqueue, hidattachmsg);
			}
		}
		if(hidattach == 1)
		{
			hidattach = 0;
			hidattached = 1;
			HIDOpen(LoaderRequest);
			memset32(AttachedDevices, 0, sizeof(usb_device_entry)*32);
			IOS_IoctlAsync(HIDHandle, GetDeviceChange, NULL, 0, AttachedDevices, 0x180, hidqueue, hidchangemsg);
		}
		VenUpdate(LoaderRequest);
		if(compdone)
		{
			compdone = 0;
			CompRead();
		}
		for(i = 0; i < HID_MAX_SLOTS; ++i)
		{
			if(Slots[i].ReadDone == 1 && (hidattached || Slots[i].IsVen))
			{
				Slots[i].ReadDone = 0;
				Slots[i].ReadPending = 0;
				if(Slots[i].Active && Slots[i].Read)
					Slots[i].Read(i);
			}
		}
		if(hidattached)
		{
			if(keyboardread == 1)
			{
				keyboardread = 0;
				KBPending = 0;
				if(KeyboardID != 0)
					KeyboardRead();
			}
			if(RumbleEnabled && RumbleSlot >= 0 && Slots[RumbleSlot].Active)
			{
				//sync_before_read((void*)MotorCommand,0x20);
				HIDRumbleCurrent = read32(MotorCommand);
				if( HIDRumbleLast != HIDRumbleCurrent )
				{
					if(HIDRumble) HIDRumble( HIDRumbleCurrent );
					HIDRumbleLast = HIDRumbleCurrent;
				}
			}
		}
                 // crashes wiivc with hid controllers connected
		//HID_Timer = read32(HW_TIMER);
	}
}
