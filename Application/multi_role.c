/******************************************************************************
 * @file  simple_ble_topology.c
 *
 * @description Application task for the Simple Topology example
 *
 *
 * Copyright (C) 2015 Texas Instruments Incorporated - http://www.ti.com/ 
 * 
 * 
 *  Redistribution and use in source and binary forms, with or without 
 *  modification, are permitted provided that the following conditions 
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright 
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright   
 *    notice, this list of conditions and the following disclaimer in the 
 *    documentation and/or other materials provided with the   
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT 
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *****************************************************************************/

/*********************************************************************
 * INCLUDES
 */
#include <string.h>

#include <ti/sysbios/knl/Task.h>
#include <ti/sysbios/knl/Clock.h>
#include <ti/sysbios/knl/Semaphore.h>
#include <ti/sysbios/knl/Queue.h>

#include "hci_tl.h"
#include "gatt.h"
#include "gapgattserver.h"
#include "gattservapp.h"

#include "bsp_i2c.h"
#include "bsp_spi.h"
//#include "sensor.h"

#include "multi.h"
#include "gapbondmgr.h"

#include "osal_snv.h"
#include "ICallBleAPIMSG.h"

#include "util.h"
#include "Board.h"

#include "linkdb.h"
#include "multi_role.h"

#include "uart_printf.h"
#include <xdc/runtime/System.h>


// How often to perform a new scan event (in msec)
#define SCAN_EVENT_PERIOD                     10000 // 10 seconds

// How long to advertise once we've started (in seconds)
#define ADV_DURATION						  4 // 4 seconds

/*********************************************************************
 * CONSTANTS
 */
// Advertising interval when device is discoverable (units of 625us, 160=100ms)
#define DEFAULT_ADVERTISING_INTERVAL          160

// Limited discoverable mode advertises for a specified amount of time, and then stops
// General discoverable mode advertises indefinitely
#define DEFAULT_DISCOVERABLE_MODE             GAP_ADTYPE_FLAGS_GENERAL

#define DEFAULT_SCAN_DURATION				  1000 // scan for one second
#define DEFAULT_SCAN_WIND					  1600 // want to be scanning the whole time
#define DEFAULT_SCAN_INT					  1600 // shouldn't matter because I want it to go off.

// Discovey mode (limited, general, all)
#define DEFAULT_DISCOVERY_MODE                DEVDISC_MODE_ALL

// Whether to report all contacts or only the first for each device
#define FILTER_ADV_REPORTS					  FALSE

// TRUE to use active scan
#define DEFAULT_DISCOVERY_ACTIVE_SCAN         FALSE

// TRUE to use white list during discovery
#define DEFAULT_DISCOVERY_WHITE_LIST          FALSE

// Task configuration
#define SBT_TASK_PRIORITY                     1

#ifndef SBT_TASK_STACK_SIZE
#define SBT_TASK_STACK_SIZE                   644
#endif

// stuff for advertisements and identification
#define NODE_ID								  { 0x02  }
#define NODE_ID_LENGTH						  1
#define ADV_PKT_ID_OFFSET					  12
#define ADV_PKT_STATE_OFFSET				  ADV_PKT_ID_OFFSET + NODE_ID_LENGTH

// Internal Events for RTOS application
#define SBT_STATE_CHANGE_EVT                  0x0001
#define SCAN_EVENT	                          0x0002

#define SNV_BASE_ID							  0x80

// the maximum number of recent neighbors to keep
#define RECENT_LIST_MAX_SIZE				  3



/*********************************************************************
 * TYPEDEFS
 */


typedef enum RUThNodeState_t {
	SCANNING,
	ADVERTISING,
	SLEEPING
} RUThNodeState_t;


// App event passed from profiles.
typedef struct
{
	uint16_t event;  // event type
	uint8_t status; // event status
	uint8_t *pData; // event data pointer
} sbtEvt_t;

typedef struct {
	uint8 mac[B_ADDR_LEN]; //!< Device's Address
	uint8 advDataLen;
	uint8 advData[31];
	uint32 lastContactTicks;
	uint8 rssi;
} myGapDevRec_t;

// define list for storing discovered RUTh neighbors
typedef struct listNode {
	myGapDevRec_t device;
	struct listNode *next;
} listNode_t;

/*********************************************************************
 * LOCAL VARIABLES
 */

// Entity ID globally used to check for source and/or destination of messages
static ICall_EntityID selfEntity;

// Semaphore globally used to post events to the application thread
static ICall_Semaphore sem;

// Queue object used for app messages
static Queue_Struct appMsg;
static Queue_Handle appMsgQueue;

// events flag for internal application events.
static uint16_t events;

// Task configuration
Task_Struct sbmTask;
Char sbmTaskStack[SBT_TASK_STACK_SIZE];

static RUThNodeState_t nodeState = SLEEPING;

// head of the list of discovered peers
static listNode_t* neighborListHeadPtr = NULL;
//list of the three most recently updated neighbors
static listNode_t* mostRecentNeighborsPtr = NULL;

static uint8 advertData[31] = {

		0x05,// length of this data
		GAP_ADTYPE_LOCAL_NAME_COMPLETE,
		'R',
		'U',
		'T',
		'h',
		0x03,// length of this data
		GAP_ADTYPE_MANUFACTURER_SPECIFIC,
		0x0D,
		0x00,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0,
		0

};

// GAP - Advertisement data (max size = 31 bytes, though this is
// best kept short to conserve power while advertisting)
//static uint8_t advertData[] =
//{
		// Flags; this sets the device to use limited discoverable
		// mode (advertises for 30 seconds at a time) instead of general
		// discoverable mode (advertises indefinitely)
		//0x02,   // length of this data
		//GAP_ADTYPE_FLAGS,
		//DEFAULT_DISCOVERABLE_MODE | GAP_ADTYPE_FLAGS_BREDR_NOT_SUPPORTED,

		// 25 byte beacon advertisement data
		// Preamble: Company ID - 0x000D for TI, refer to https://www.bluetooth.org/en-us/specification/assigned-numbers/company-identifiers
		// Data type: Beacon (0x02)
		// Data length: 0x15
		// UUID: 00000000-0000-0000-0000-000000000000 (null beacon)
		// Major: 1 (0x0001)
		// Minor: 1 (0x0001)
		// Measured Power: -59 (0xc5)
		//0x1A, // length of this data including the data type byte
		//GAP_ADTYPE_MANUFACTURER_SPECIFIC, // manufacturer specific adv data type
		//0x0D, // Company ID - Fixed
		//0x00, // Company ID - Fixed
		//0x02, // Data Type - Fixed
		//0x15, // Data Length - Fixed
		//0x00, // UUID - Variable based on different use cases/applications
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // UUID
		//0x00, // Major
		//0x01, // Major
		//0x00, // Minor
		//0x01, // Minor
		//0xc5  // Power - The 2's complement of the calibrated Tx Power
//};

// Pins that are actively used by the application
static PIN_Config SensortagAppPinTable[] =
{
    Board_LED1       | PIN_GPIO_OUTPUT_EN | PIN_GPIO_LOW | PIN_PUSHPULL | PIN_DRVSTR_MAX,     /* LED initially off             */
    Board_LED2       | PIN_GPIO_OUTPUT_EN | PIN_GPIO_LOW | PIN_PUSHPULL | PIN_DRVSTR_MAX,     /* LED initially off             */
    PIN_TERMINATE
};

// Global pin resources
PIN_State pinGpioState;
PIN_Handle hGpioPin;

// Scanning state
static bool scanningStarted = FALSE;

static uint8_t advertising_enabled = FALSE;

static Clock_Struct scanClock;

static uint8 myIDArray[] = {0x00};//NODE_ID;
static uint8 broadcastID[] = { 0xFF };
static uint32 batteryLev = 0;


/*********************************************************************
 * LOCAL FUNCTIONS
 */
static void simpleTopology_init( void );
static void simpleTopology_taskFxn(UArg a0, UArg a1);
static uint8_t simpleTopology_processStackMsg(ICall_Hdr *pMsg);
static void simpleTopology_processAppMsg(sbtEvt_t *pMsg);
static void simpleTopology_processRoleEvent(gapMultiRoleEvent_t *pEvent);
static uint8_t simpleTopology_enqueueMsg(uint16_t event, uint8_t status, uint8_t *pData);
static uint8_t simpleTopology_eventCB(gapMultiRoleEvent_t *pEvent);
static void SensorTagMultiRoleTest_scanStartHandler(UArg arg);

static uint8 memcomp(uint8 * str1, uint8 * str2, uint8 len);

static bool RUTh_isRUThNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent_a);
static bool RUTh_isInNeighborList(gapDeviceInfoEvent_t *gapDeviceInfoEvent);
static listNode_t* RUTh_getNeighbor(uint8 *addr);
static listNode_t* RUTh_addNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent);
static uint8 RUTh_countNeighbors();
static void RUTh_updateDiscoveryTime(gapDeviceInfoEvent_t *gapDeviceInfoEvent);
static listNode_t* RUTh_addMostRecentNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent);
static void RUTh_updateAdvertData();
static void RUTh_processAdvertisement(gapMultiRoleEvent_t *pEvent);


/*********************************************************************
 * PROFILE CALLBACKS
 */

// GAP Role Callbacks
static gapRolesCBs_t simpleTopology_gapRoleCBs =
{
		simpleTopology_eventCB,        // events to be handled by the app are passed through the GAP Role here
};

/*********************************************************************
 * PUBLIC FUNCTIONS
 */

/*********************************************************************
 * @fn      simpleTopology_createTask
 *
 * @brief   Task creation function for the Simple BLE Peripheral.
 *
 * @param   None.
 *
 * @return  None.
 */
void SimpleTopology_createTask(void)
{
	Task_Params taskParams;

	// Configure task
	Task_Params_init(&taskParams);
	taskParams.stack = sbmTaskStack;
	taskParams.stackSize = SBT_TASK_STACK_SIZE;
	taskParams.priority = SBT_TASK_PRIORITY;

	Task_construct(&sbmTask, simpleTopology_taskFxn, &taskParams, NULL);
}

/*********************************************************************
 * @fn      simpleTopology_init
 *
 * @brief   Called during initialization and contains application
 *          specific initialization (ie. hardware initialization/setup,
 *          table initialization, power up notification, etc), and
 *          profile kjinitialization/setup.
 *
 * @param   None.
 *
 * @return  None.
 */
static void simpleTopology_init(void)
{
	// Setup I2C for sensors
	bspI2cInit();

	// Handling of buttons, LED, relay
	hGpioPin = PIN_open(&pinGpioState, SensortagAppPinTable);

	// ******************************************************************
	// N0 STACK API CALLS CAN OCCUR BEFORE THIS CALL TO ICall_registerApp
	// ******************************************************************
	// Register the current thread as an ICall dispatcher application
	// so that the application can send and receive messages.
	ICall_registerApp(&selfEntity, &sem);

	// Create an RTOS queue for message from profile to be sent to app.
	appMsgQueue = Util_constructQueue(&appMsg);

	Util_constructClock(&scanClock, SensorTagMultiRoleTest_scanStartHandler,
			SCAN_EVENT_PERIOD, SCAN_EVENT_PERIOD, TRUE, SCAN_EVENT);

	//read ID
	osal_snv_read(SNV_BASE_ID, NODE_ID_LENGTH, myIDArray);
	memcpy(&advertData[ADV_PKT_ID_OFFSET], myIDArray, NODE_ID_LENGTH);

	// Setup the GAP
	{
		/*-------------------PERIPHERAL-------------------*/
		uint16_t advInt = DEFAULT_ADVERTISING_INTERVAL;
		GAP_SetParamValue(TGAP_LIM_DISC_ADV_INT_MIN, advInt);
		GAP_SetParamValue(TGAP_LIM_DISC_ADV_INT_MAX, advInt);
		GAP_SetParamValue(TGAP_GEN_DISC_ADV_INT_MIN, advInt);
		GAP_SetParamValue(TGAP_GEN_DISC_ADV_INT_MAX, advInt);

		GAP_SetParamValue(TGAP_LIM_ADV_TIMEOUT, ADV_DURATION);

		/*-------------------CENTRAL-------------------*/
		GAP_SetParamValue(TGAP_GEN_DISC_SCAN, DEFAULT_SCAN_DURATION);
		GAP_SetParamValue(TGAP_GEN_DISC_SCAN_INT, DEFAULT_SCAN_INT);
		GAP_SetParamValue(TGAP_GEN_DISC_SCAN_WIND, DEFAULT_SCAN_WIND);
		GAP_SetParamValue(TGAP_LIM_DISC_SCAN_INT, DEFAULT_SCAN_INT);
		GAP_SetParamValue(TGAP_LIM_DISC_SCAN_WIND, DEFAULT_SCAN_WIND);
	}

	// Setup the GAP Role Profile
	{
		/*--------PERIPHERAL-------------*/
		// For all hardware platforms, device starts advertising upon initialization
		uint8_t initialAdvertEnable = FALSE;
		// By setting this to zero, the device will go into the waiting state after
		// being discoverable for 30.72 second, and will not being advertising again
		// until the enabler is set back to TRUE
		uint16_t advertOffTime = 0;

		GAPRole_SetParameter(GAPROLE_ADVERT_ENABLED, sizeof(uint8_t),
				&initialAdvertEnable, NULL);
		GAPRole_SetParameter(GAPROLE_ADVERT_OFF_TIME, sizeof(uint16_t),
				&advertOffTime, NULL);
		GAPRole_SetParameter(GAPROLE_ADVERT_DATA, sizeof(advertData), advertData, NULL);

		// Register with GAP for HCI/Host messages
		GAP_RegisterForMsgs(selfEntity);
	}

	VOID GAPRole_StartDevice(&simpleTopology_gapRoleCBs);
}

/*********************************************************************
 * @fn      simpleTopology_taskFxn
 *
 * @brief   Application task entry point for the Simple BLE Multi.
 *
 * @param   a0, a1 - not used.
 *
 * @return  None.
 */
static void simpleTopology_taskFxn(UArg a0, UArg a1)
{
	// Initialize application
	simpleTopology_init();

	// Application main loop
	for (;;)
	{
		// Waits for a signal to the semaphore associated with the calling thread.
		// Note that the semaphore associated with a thread is signaled when a
		// message is queued to the message receive queue of the thread or when
		// ICall_signal() function is called onto the semaphore.
		ICall_Errno errno = ICall_wait(ICALL_TIMEOUT_FOREVER);

		if (errno == ICALL_ERRNO_SUCCESS)
		{
			ICall_EntityID dest;
			ICall_ServiceEnum src;
			ICall_HciExtEvt *pMsg = NULL;

			if (ICall_fetchServiceMsg(&src, &dest,
					(void **)&pMsg) == ICALL_ERRNO_SUCCESS)
			{
				uint8 safeToDealloc = TRUE;

				if ((src == ICALL_SERVICE_CLASS_BLE) && (dest == selfEntity))
				{
					// Process inter-task message
					safeToDealloc = simpleTopology_processStackMsg((ICall_Hdr *)pMsg);
				}

				if (pMsg && safeToDealloc)
				{
					ICall_freeMsg(pMsg);
				}
			}

			// If RTOS queue is not empty, process app message.
			while (!Queue_empty(appMsgQueue))
			{
				sbtEvt_t *pMsg = (sbtEvt_t *)Util_dequeueMsg(appMsgQueue);
				if (pMsg)
				{
					// Process message.
					simpleTopology_processAppMsg(pMsg);

					// Free the space from the message.
					ICall_free(pMsg);
				}
			}
		}

		// the trigger was a periodic event
		// trigger was the SCAN_EVENT
		if (!!(events & SCAN_EVENT))
		{
			// effectively mark off the event as "handled"
			events &= ~SCAN_EVENT;
			// now start discovery.
			// CJ: I think that the scan parameters are set in such a way
			// that it will start and stop itself
			scanningStarted = true;
			IntMasterDisable();
			System_printf("Start Scanning!\n");
			IntMasterEnable();

			GAPRole_StartDiscovery(DEFAULT_DISCOVERY_MODE, DEFAULT_DISCOVERY_ACTIVE_SCAN,
					DEFAULT_DISCOVERY_WHITE_LIST);
		}
	}
}

/*********************************************************************
 * @fn      simpleTopology_processStackMsg
 *
 * @brief   Process an incoming stack message.
 *
 * @param   pMsg - message to process
 *
 * @return  TRUE if safe to deallocate incoming message, FALSE otherwise.
 */
static uint8_t simpleTopology_processStackMsg(ICall_Hdr *pMsg)
{
	uint8_t safeToDealloc = TRUE;

	switch (pMsg->event)
	{
	case GAP_MSG_EVENT:
		simpleTopology_processRoleEvent((gapMultiRoleEvent_t *)pMsg);
		break;

	default:
		// do nothing
		break;
	}

	return (safeToDealloc);
}


/*********************************************************************
 * @fn      simpleTopology_processAppMsg
 *
 * @brief   Process an incoming callback from a profile.
 *
 * @param   pMsg - message to process
 *
 * @return  None.
 */
static void simpleTopology_processAppMsg(sbtEvt_t *pMsg)
{
	switch (pMsg->event)
	{
	case SBT_STATE_CHANGE_EVT:
		simpleTopology_processStackMsg((ICall_Hdr *)pMsg->pData);
		// Free the stack message
		ICall_freeMsg(pMsg->pData);
		break;

	default:
		// Do nothing.
		break;
	}
}

/*********************************************************************
 * @fn      simpleTopology_eventCB
 *
 * @brief   Central event callback function.
 *
 * @param   pEvent - pointer to event structure
 *
 * @return  TRUE if safe to deallocate event message, FALSE otherwise.
 */
static uint8_t simpleTopology_eventCB(gapMultiRoleEvent_t *pEvent)
{
	// Forward the role event to the application
	if (simpleTopology_enqueueMsg(SBT_STATE_CHANGE_EVT, SUCCESS, (uint8_t *)pEvent))
	{
		// App will process and free the event
		return FALSE;
	}

	// Caller should free the event
	return TRUE;
}

/*********************************************************************
 * @fn      simpleTopology_processRoleEvent
 *
 * @brief   Multi role event processing function.
 *
 * @param   pEvent - pointer to event structure
 *
 * @return  none
 */
static void simpleTopology_processRoleEvent(gapMultiRoleEvent_t *pEvent)
{
	IntMasterDisable();
	System_printf("processRoleEvent!\n");
	IntMasterEnable();
	switch (pEvent->gap.opcode)
	{
	case GAP_END_DISCOVERABLE_DONE_EVENT:
	{
		IntMasterDisable();
		System_printf("Done Advertising!\n");
		IntMasterEnable();
	}
	break;

	case GAP_DEVICE_DISCOVERY_EVENT:
	{
		// discovery complete
		scanningStarted = FALSE;
		IntMasterDisable();
		System_printf("Done Scanning.\n");
		System_printf("I've discovered %d nodes to date.\n", RUTh_countNeighbors());
		System_printf("Starting Advertising!\n");


		RUTh_updateAdvertData();

		IntMasterEnable();


		advertising_enabled = TRUE;
		GAPRole_SetParameter(GAPROLE_ADVERT_ENABLED, sizeof(uint8_t), &advertising_enabled, NULL);

	}
	break;
	case GAP_DEVICE_INFO_EVENT:
	{
		if (pEvent->deviceInfo.eventType == GAP_ADRPT_ADV_SCAN_IND | //adv data event (Scannable undirected)
					pEvent->deviceInfo.eventType == GAP_ADRPT_ADV_IND      |
					pEvent->deviceInfo.eventType == GAP_ADRPT_ADV_NONCONN_IND) { //adv data event (Connectable undirected)

			IntMasterDisable();
			System_printf("Received advertisement!\n");
			RUTh_processAdvertisement(pEvent);

			IntMasterEnable();
		}
	}

	default:
		break;
	}
}

/*********************************************************************
 * @fn      simpleTopology_enqueueMsg
 *
 * @brief   Creates a message and puts the message in RTOS queue.
 *
 * @param   event - message event.
 * @param   state - message state.
 *
 * @return  None.
 */
static uint8_t simpleTopology_enqueueMsg(uint16_t event, uint8_t status, uint8_t *pData)
{
	sbtEvt_t *pMsg = ICall_malloc(sizeof(sbtEvt_t));

	// Create dynamic pointer to message.
	if (pMsg)
	{
		pMsg->event = event;
		pMsg->status = status;
		pMsg->pData = pData;

		// Enqueue the message.
		return Util_enqueueMsg(appMsgQueue, sem, (uint8*)pMsg);
	}

	return FALSE;
}




/*******************************************************************************
 * @fn      SensorTagMultiRoleTest_scanStartHandler
 *
 * @brief   Handler function for clock time-outs.
 *
 * @param   arg - event type
 *
 * @return  none
 */
static void SensorTagMultiRoleTest_scanStartHandler(UArg arg)
{
	// Store the event.
	events |= arg;

	// we don't want to do work here, though, because of the priority problem
	// so once we've posted the event, wake up the application and let the app thread do the work

	// Wake up the application.
	Semaphore_post(sem);
}

/*********************************************************************
 *********************************************************************/



/*********************************************************************
 * @fn      isRUThNode
 *
 * @brief	checks if the gap event is related to a RUTh node or not
 *
 * @param	pointer to gap info event
 *
 * @return  bool
 */

static bool RUTh_isRUThNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent_a) {
	uint8 index = 0;

	if (gapDeviceInfoEvent_a->eventType == GAP_ADRPT_ADV_SCAN_IND |
		gapDeviceInfoEvent_a->eventType == GAP_ADRPT_ADV_IND      |
		gapDeviceInfoEvent_a->eventType == GAP_ADRPT_ADV_NONCONN_IND) { //only in advertisements

		while (index < gapDeviceInfoEvent_a->dataLen) {
			if (gapDeviceInfoEvent_a->pEvtData[index + 1]
					== GAP_ADTYPE_LOCAL_NAME_COMPLETE) { // found the name

				if (memcomp(&(gapDeviceInfoEvent_a->pEvtData[index + 2]),&(advertData[2]),(gapDeviceInfoEvent_a->pEvtData[index]) - 1)) { //it's a compatible name

					return TRUE;

				}
			}
			return FALSE;
		}
	}
	return FALSE;
}

/*********************************************************************
 * @fn      memcomp
 *
 * @brief
 *
 * @param
 *
 * @return
 */

static uint8 memcomp(uint8 * str1, uint8 * str2, uint8 len) {
	uint8 index;
	for (index = 0; index < len; index++) {
		if (str1[index] != str2[index]) {
			return 0;
		}
	}
	return 1;
}

/*********************************************************************
 * @fn      RUTh_addNode
 *
 * @brief	Adds a node at the end of the neighbor list with informations contained in the gap info event.
 * It automatically manages the adding of first node which is critical because it is referenced by
 * neighborListHeadPtr
 *
 * @return  The pointer to the node istance inside the list
 */
static listNode_t* RUTh_addNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent) {

	listNode_t* new_Node_Ptr = (listNode_t*) ICall_malloc(sizeof(listNode_t));

	if (new_Node_Ptr == NULL) {
		//malloc fail!
		PIN_setOutputValue(hGpioPin, Board_LED1, Board_LED_ON);
		PIN_setOutputValue(hGpioPin, Board_LED2, Board_LED_ON);
		return NULL;
	}

	//set up the data for the new node
	new_Node_Ptr->device.rssi = gapDeviceInfoEvent->rssi;
	new_Node_Ptr->device.lastContactTicks = Clock_getTicks();
	new_Node_Ptr->device.advDataLen = gapDeviceInfoEvent->dataLen;

	memcpy(new_Node_Ptr->device.mac, gapDeviceInfoEvent->addr, B_ADDR_LEN);
	memcpy(new_Node_Ptr->device.advData, &gapDeviceInfoEvent->pEvtData[0], gapDeviceInfoEvent->dataLen);

	new_Node_Ptr->next = NULL; // we put the new node at the back of the list

	// add the new node at the end of the list
	if(neighborListHeadPtr != NULL){
		listNode_t* node = neighborListHeadPtr;
		while (node->next != NULL){
			node = node->next;
		}
		node->next = new_Node_Ptr;
	}
	else{
		neighborListHeadPtr = new_Node_Ptr;
	}

	// if we're adding this new guy, he's also the most recently discovered, so we need to add him to that other list, too
	RUTh_addMostRecentNode(gapDeviceInfoEvent);

	return new_Node_Ptr;
}

/*********************************************************************
 * @fn      RUTh_addMostRecentNode
 *
 * @brief	Maintains a list of the most recent nodes seen, limited by a constant RECENT_LIST_MAX_SIZE
 *
 * @return  The pointer to the node istance inside the list
 */
static listNode_t* RUTh_addMostRecentNode(gapDeviceInfoEvent_t *gapDeviceInfoEvent) {

	listNode_t* new_Node_for_Recents_Ptr = (listNode_t*) ICall_malloc(sizeof(listNode_t));

	if (new_Node_for_Recents_Ptr == NULL) {
		//malloc fail!
		PIN_setOutputValue(hGpioPin, Board_LED1, Board_LED_ON);
		PIN_setOutputValue(hGpioPin, Board_LED2, Board_LED_ON);
		return NULL;
	}

	//set up the data for the new node
	new_Node_for_Recents_Ptr->device.rssi = gapDeviceInfoEvent->rssi;
	new_Node_for_Recents_Ptr->device.lastContactTicks = Clock_getTicks();
	new_Node_for_Recents_Ptr->device.advDataLen = gapDeviceInfoEvent->dataLen;

	memcpy(new_Node_for_Recents_Ptr->device.mac, gapDeviceInfoEvent->addr, B_ADDR_LEN);
	memcpy(new_Node_for_Recents_Ptr->device.advData, &gapDeviceInfoEvent->pEvtData[0], gapDeviceInfoEvent->dataLen);

	// since we're adding this guy, he's one of the three most recent. So we update that list
	new_Node_for_Recents_Ptr->next = mostRecentNeighborsPtr;
	mostRecentNeighborsPtr = new_Node_for_Recents_Ptr;

	//if this list is longer than its limit, then we need to drop whoever's at the end...
	listNode_t* node = mostRecentNeighborsPtr;
	uint8 index = 1;
	while(node != NULL && index != RECENT_LIST_MAX_SIZE){
		node = node->next;
		index++;
	}
	// node is pointing to either NULL or the node that should be the last one.
	// if node is not null and node->next is not null, we need to deallocate node->next and set node->next to null.
	if(node != NULL){
		if(node->next != NULL){
			ICall_free(node->next);
			node->next = NULL;
		}
	}

	return new_Node_for_Recents_Ptr;
}


/*********************************************************************
 * @fn      RUTh_isInNeighorList
 *
 * @brief	Checks whether the device referenced in the gapDeviceInfoEvent is already a known neighbor
 *
 * @return  true if the reference node is in the list; false otherwise
 */
static bool RUTh_isInNeighborList(gapDeviceInfoEvent_t *gapDeviceInfoEvent) {
	bool toReturn = false;
	if(neighborListHeadPtr != NULL){
		listNode_t* node = neighborListHeadPtr;
		while(node != NULL){
			if(memcomp(node->device.mac, gapDeviceInfoEvent->addr, B_ADDR_LEN)){
				toReturn = true;
				break;
			}
			node = node->next;
		}
	}
	return toReturn;
}

/*********************************************************************
 * @fn      RUTh_removeFromRecentsList
 *
 * @brief	Checks whether the device referenced in the gapDeviceInfoEvent is one of the recent
 *          neighbors and if so, deletes it.
 *
 * @return  true if the reference node was in the list and was deleted; false otherwise
 */
static bool RUTh_removeFromRecentList(gapDeviceInfoEvent_t *gapDeviceInfoEvent) {
	bool toReturn = false;
	if(mostRecentNeighborsPtr != NULL){
		// if the first one is the match, it's a special case...
		if(memcomp(mostRecentNeighborsPtr->device.mac, gapDeviceInfoEvent->addr, B_ADDR_LEN)){
			toReturn = true;
			listNode_t* nodeToDelete = mostRecentNeighborsPtr;
			mostRecentNeighborsPtr = nodeToDelete->next;
			ICall_free(nodeToDelete);
		}
		else{
			listNode_t* node = mostRecentNeighborsPtr;
			while(node->next != NULL){
				if(memcomp(node->next->device.mac, gapDeviceInfoEvent->addr, B_ADDR_LEN)){
					toReturn = true;
					listNode_t* nodeToDelete = node->next;
					node->next = nodeToDelete->next;
					ICall_free(nodeToDelete);
					break;
				}
				node = node->next;
			}
		}
	}
	return toReturn;
}

/*********************************************************************
 * @fn      RUTh_getNeighbor
 *
 * @brief	uses a bt mac address to find a stored neighbor node
 *
 * @return  a pointer to a node if it exists in the list
 */
static listNode_t* RUTh_getNeighbor(uint8 *addr) {
	if(neighborListHeadPtr != NULL){
		listNode_t* node = neighborListHeadPtr;
		while(node != NULL){
			if(memcomp(node->device.mac, addr, B_ADDR_LEN)){
				return node;
			}
			node = node->next;
		}
	}
	return NULL;
}

/*********************************************************************
 * @fn      RUTh_countNeighbors
 *
 * @brief	Counts the number of discovered neighbors
 *
 * @return  the number of nodes in the neighborlist
 */
static uint8 RUTh_countNeighbors(){
	uint8 toReturn = 0;
	listNode_t* node = neighborListHeadPtr;
	while(node != NULL){
		toReturn++;
		node = node->next;
	}
	return toReturn;
}

/*********************************************************************
 * @fn      RUTh_updateDiscoveryTime
 *
 * @brief	updates the discovery time of an already known neighbor
 *
 */
static void RUTh_updateDiscoveryTime(gapDeviceInfoEvent_t *gapDeviceInfoEvent){
	listNode_t* node = RUTh_getNeighbor(gapDeviceInfoEvent->addr);
	if(node != NULL){
		node->device.lastContactTicks = Clock_getTicks();
	}
	// if I updated the discovery time to now, this node is now one of the most recent ones.
	// so I need to update that data structure too.
	// first, it's possible that this node is already in that list. We wouldn't want it there twice.
	// remove it if its there
	RUTh_removeFromRecentList(gapDeviceInfoEvent);
	// then add the updated info
	RUTh_addMostRecentNode(gapDeviceInfoEvent);
}

static void RUTh_updateAdvertData(){
	uint8 newAdvertData[31];
	uint8 numNeighbors;
	uint8 index;


	newAdvertData[0] = advertData[0];
	newAdvertData[1] = advertData[1];
	newAdvertData[2] = advertData[2];
	newAdvertData[3] = advertData[3];
	newAdvertData[4] = advertData[4];
	newAdvertData[5] = advertData[5];
	newAdvertData[6] = advertData[6];
	newAdvertData[7] = advertData[7];
	newAdvertData[8] = advertData[8];
	newAdvertData[9] = advertData[9];

	//newAdvertData[10] -- needs to be length of the RUTh application data. set it later.

	numNeighbors = RUTh_countNeighbors();

	newAdvertData[11] = numNeighbors;

	if(numNeighbors >= RECENT_LIST_MAX_SIZE){
		newAdvertData[12] = RECENT_LIST_MAX_SIZE;
	}
	else{
		newAdvertData[12] = numNeighbors;
	}

	index = 13;
	listNode_t* node = mostRecentNeighborsPtr;
	while(node != NULL){
		uint8 i = 0;
		while(i < B_ADDR_LEN){
			newAdvertData[index++] = node->device.mac[i++];
		}
		node = node->next;
	}
	// the last byte we filled is (index - 1); the size of the data is index - 11
	newAdvertData[10] = (index - 11);
	GAP_UpdateAdvertisingData(selfEntity, true, index, &newAdvertData[0]);
	System_printf("adv[0]: %d\n", newAdvertData[0]);
	System_printf("adv[1]: %d\n", newAdvertData[1]);
	System_printf("adv[2]: %c\n", newAdvertData[2]);
	System_printf("adv[3]: %c\n", newAdvertData[3]);
	System_printf("adv[4]: %c\n", newAdvertData[4]);
	System_printf("adv[5]: %c\n", newAdvertData[5]);
	System_printf("adv[6]: %d\n", newAdvertData[6]);
	System_printf("adv[7]: %d\n", newAdvertData[7]);
	System_printf("adv[8]: %d\n", newAdvertData[8]);
	System_printf("adv[9]: %d\n", newAdvertData[9]);
	System_printf("adv[10]: %d\n", newAdvertData[10]);
	System_printf("adv[11]: %d\n", newAdvertData[11]);
	System_printf("adv[12]: %d\n", newAdvertData[12]);
	System_printf("adv[13]: %d\n", newAdvertData[13]);
	System_printf("adv[14]: %d\n", newAdvertData[14]);
}

static void RUTh_processAdvertisement(gapMultiRoleEvent_t *pEvent){
	System_printf("Address: ");
	System_printf(Util_convertBdAddr2Str(pEvent->deviceInfo.addr));
	System_printf("\n");
	if(RUTh_isRUThNode((gapDeviceInfoEvent_t*) &pEvent->deviceInfo)){
		System_printf("RUTh Node! Adding to list if it's not already there.\n");
		// add a newly discovered neighbor to the list
		if(!RUTh_isInNeighborList((gapDeviceInfoEvent_t*) &pEvent->deviceInfo)){
			RUTh_addNode((gapDeviceInfoEvent_t*) &pEvent->deviceInfo);
		}
		// if the neighbor was already known, just update the clockticks
		else{
			RUTh_updateDiscoveryTime((gapDeviceInfoEvent_t*) &pEvent->deviceInfo);
		}

		//Just for fun, let's see what's in the advert data. It should be (from byte 10):
		// length of app data (one byte)
		// number of neighbors (one byte)
		// number of neighbors included (up to three; one byte)
		// addresses of neighbors (6 bytes each)
		System_printf("How  much data is there? %x\n", pEvent->deviceInfo.dataLen);
		//Let's look at some of it
		System_printf("adv[0]: %d\n", pEvent->deviceInfo.pEvtData[0]);
		System_printf("adv[1]: %d\n", pEvent->deviceInfo.pEvtData[1]);
		System_printf("adv[2]: %c\n", pEvent->deviceInfo.pEvtData[2]);
		System_printf("adv[3]: %c\n", pEvent->deviceInfo.pEvtData[3]);
		System_printf("adv[4]: %c\n", pEvent->deviceInfo.pEvtData[4]);
		System_printf("adv[5]: %c\n", pEvent->deviceInfo.pEvtData[5]);
		System_printf("adv[6]: %d\n", pEvent->deviceInfo.pEvtData[6]);
		System_printf("adv[7]: %d\n", pEvent->deviceInfo.pEvtData[7]);
		System_printf("adv[8]: %d\n", pEvent->deviceInfo.pEvtData[8]);
		System_printf("adv[9]: %d\n", pEvent->deviceInfo.pEvtData[9]);
		System_printf("adv[10]: %d\n", pEvent->deviceInfo.pEvtData[10]);
		System_printf("adv[11]: %d\n", pEvent->deviceInfo.pEvtData[11]);
		System_printf("adv[12]: %d\n", pEvent->deviceInfo.pEvtData[12]);
		System_printf("adv[13]: %d\n", pEvent->deviceInfo.pEvtData[13]);
		System_printf("adv[14]: %d\n", pEvent->deviceInfo.pEvtData[14]);


	}
}
