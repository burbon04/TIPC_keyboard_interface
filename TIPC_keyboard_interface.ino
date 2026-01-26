#include <avr/interrupt.h>
#include <avr/pgmspace.h>
#include <Arduino.h>
#include <util/delay_basic.h>

//
// TIPC keyboard interface with USB/PS2 communication bridge
// https://github.com/burbon04/TIPC_keyboard_interface
// Dec 2025 / Jan 2026 - v1.0, initial release, burbon04 <at> gmx.de       
//
//
// Limitations:
// - all timings are done in software on a single MCU, so if typing too fast USB/PS2 signals get skipped
// - intentionally not all keys are emulated as modern keyboards are quite different to original TIPC keyboards
// - I did not implement CAPS LOCK, the most annyoing key ever ;)
// - PS/2 protocol keyboard required, USB keyboard supported as long it supports PS/2 mode
// - NO keyboard LED support yet
//
// -- NO WARRANTY DISCLAIMER - THIS SOFTWARE IS PROVIDED AS IS, USE AT YOUR OWN RISK --
//


///////////////////
// PIN assignments
///////////////////

const int kbdirq    =  2;  // USB D+ line or PS/2 clock
const int tipcrx    =  3;  // our RX connects to TIPC TX
const int ledgreen  =  4;  // key code send activity
const int ledyellow =  5;  // command receive activity
const int kbddata   =  8;  // USB D- line or PS/2 data
const int tipctx    =  9;  // our TX connects to TIPC RX

////////////////////////////////////////////////////////////////////
// keyboard related stuff and USB/PS2 interface 
// buffer and signal logic heavily borrowed from PS2keyboard library
////////////////////////////////////////////////////////////////////

#define SCANCODEBUFFER 64
const uint8_t  kbdctrl  = 0;
const uint8_t  kbdalt   = 1;
const uint8_t  kbdshift = 2;
const uint8_t  kbdcaps   = 7;
static bool    keystop=false;
static bool    keyext=false;
static uint8_t keypause=0;
static uint8_t modebyte=0b1111000;
static uint8_t modebyteprev=0;   // always initialize first
static uint8_t sendkey;

static char    tipcchar;
static uint8_t keyin;

static volatile uint8_t kbdbuffer[SCANCODEBUFFER];
static volatile uint8_t kbdhead, kbdtail;
static uint8_t CharBuffer=0;
static uint8_t UTF8next=0;


static inline uint8_t get_scan_code(void)    
{
  uint8_t c, i;

  i = kbdtail;
  if (i == kbdhead) return 0;
  i++;
  if (i >= SCANCODEBUFFER) i = 0;
  c = kbdbuffer[i];
  kbdtail = i;
  return c;
}

void kbdin_interrupt(void)  
{
  static uint8_t bitcount=0;
  static uint8_t incoming=0;
  static uint32_t prev_ms=0;
  static uint32_t now_ms;
  static uint8_t n, val;

  val = digitalRead(kbddata);    
  now_ms = millis();
  if (now_ms - prev_ms > 250) {
    bitcount = 0;
    incoming = 0;
  }
  prev_ms = now_ms;
  n = bitcount - 1;
  if (n <= 7) {
    incoming |= (val << n);
  }
  bitcount++;
  if (bitcount == 11) {
    uint8_t i = kbdhead + 1;
    if (i >= SCANCODEBUFFER) i = 0;
    if (i != kbdtail) {
      kbdbuffer[i] = incoming;
      kbdhead = i;
    }
    bitcount = 0;
    incoming = 0;
  }
}

////////////////////////////////////////////////////////
// PS2 scan code to TIPC key number translation tables
// based on TI PC technical referene dated 1984
////////////////////////////////////////////////////////

// regular scan codes
byte scancodes[256] = {
// 0-9
0,5,0,1,103,101,102,8,0,6,
// 10-19
4,2,104,49,0,0,0,0,0,0,
// 20-29
0,50,9,0,0,0,82,67,66,51,
// 30-39
10,0,0,84,83,68,52,12,11,0,
// 40-49
0,81,85,69,54,53,13,0,0,87,
// 50-59
86,71,70,55,14,0,0,0,88,72,
// 60-69
56,15,16,0,0,89,73,57,58,18,
// 70-79
17,0,0,91,92,74,75,59,19,0,
// 80-89
0,0,76,0,60,20,0,0,0,0,
// 90-99
77,61,0,0,0,0,0,0,0,0,
// 100-109
0,0,21,0,0,27,0,31,39,0,
// 110-119
0,0,29,42,35,32,41,40,65,0,
// 120-129
7,24,43,34,0,33,0,0,0,0,
// 130-139
0,3,0,0,0,0,0,0,0,0,
// 140-149
0,0,0,0,0,0,0,0,0,0,
// 150-159
0,0,0,0,0,0,0,0,0,0,
// 160-169
0,0,0,0,0,0,0,0,0,0
};

// extended scan codes
byte extcodes[256] = {
// 0-9
0,0,0,0,0,0,0,8,0,0,
// 10-19
0,0,0,0,0,0,0,0,90,0,
// 20-29
0,0,0,0,0,0,0,0,0,0,
// 30-39
0,0,0,0,0,0,0,0,0,0,
// 40-49
0,0,0,0,0,0,0,0,0,0,
// 50-59
0,0,0,0,0,0,0,0,0,0,
// 60-69
0,0,0,0,0,0,0,0,0,0,
// 70-79
0,0,0,0,0,0,0,0,0,0,
// 80-89
0,0,0,0,0,0,0,0,0,0,
// 90-99
30,0,0,0,0,0,0,0,0,0,
// 100-109
0,0,0,0,0,0,0,79,80,0,
// 110-119
0,0,47,48,96,0,46,64,0,0,
// 120-129
0,0,0,0,0,0,0,0,0,0,
// 130-139
0,0,0,0,0,0,0,0,0,0,
// 140-149
0,0,0,0,0,0,0,0,0,0,
// 150-159
0,0,0,0,0,0,0,0,0,0,
// 160-169
0,0,0,0,0,0,0,0,0,0
};

// PS/2 Break/Pause sequence
byte brkcode[8] = {
  0xe1, 0x14, 0x77, 0xe1, 0xf0, 0x14, 0xf0, 0x77
};

//////////////////////////////////////////////////////////////
// TIPC keyboard interface with inverted UART
// timing and buffer logic derived from SoftwareSerial library
//////////////////////////////////////////////////////////////

#define _SS_MAX_RX_BUFF 64
static uint8_t receive_buffer[_SS_MAX_RX_BUFF];
static uint8_t receive_buffer_head;
static uint8_t receive_buffer_tail;

static uint16_t rx_delay_centering = 0;
static uint16_t rx_delay_intrabit = 0;
static uint16_t rx_delay_stopbit = 0;
static uint16_t tx_delay = 0;
static uint16_t rx_bit_delay = 0;
static uint16_t tx_bit_delay = 0;

uint16_t subtract_cap(uint16_t num, uint16_t sub) {
  if (num > sub)
    return num - sub;
  else
    return 1;
}

// we need parity on TIPC RX/TX, so add a function for that
unsigned char parity(unsigned char checkno)
{
  unsigned char ones = 0;
  while(checkno != 0)
  {
    ones++;
    checkno &= (checkno-1); 
  }
  return (ones & 1);
}

// our interrupt handler that gets triggered on PIN HIGH
void tipcrx_interrupt(void)
{
   volatile uint8_t d = 0;
   volatile uint8_t p = 0;
   volatile uint8_t rpar = 0;
   volatile uint8_t oldSREG = SREG;

   if (digitalRead(tipcrx))
   {
  
     // calibrate to the expected middle of the bit signal
     _delay_loop_2(rx_delay_centering);
 
     // then read 8 bits
     for (uint8_t i=8; i > 0; --i)
     {
       _delay_loop_2(rx_delay_intrabit);
       d >>= 1;       
       if (digitalRead(tipcrx))
         d |= 0x80;
     }
 
     // and read the parity bit
     _delay_loop_2(rx_delay_intrabit);
     p = !digitalRead(tipcrx);   
     d = ~d;   // inverted UART

     // calculate parity over data bits
     rpar=parity(d);

     // and fill the buffer if valid data received
     uint8_t next = (receive_buffer_tail + 1) % _SS_MAX_RX_BUFF;
     if (next != receive_buffer_head)
     {
       rpar=parity(d);
       // if parity error -> send debug log to console (if connected)
       if (rpar != p)
            {
              Serial.println("TIPC RX parity error");
            } else {       
       receive_buffer[receive_buffer_tail] = d;
       receive_buffer_tail = next;
            }
     }
      
     // wait for the stop bit to pass 
     _delay_loop_2(rx_delay_stopbit);
      
     // we are done here

  }
}

// get received character from the buffer
int tipc_read()
{
  // Empty buffer?
  if (receive_buffer_head == receive_buffer_tail)
    return -1;
    
  // Read from "head"
  uint8_t d = receive_buffer[receive_buffer_head]; // grab next byte
  receive_buffer_head = (receive_buffer_head + 1) % _SS_MAX_RX_BUFF;
  return d;
}

// check if we did receive any commands from TIPC
int tipc_avail()
{
  return ((unsigned int)(receive_buffer_tail + _SS_MAX_RX_BUFF - receive_buffer_head)) % _SS_MAX_RX_BUFF;
}

// emulate the keyboard (i.e. send keyboard codes using inverted UART to TIPC)
void tipc_send(uint8_t b)
{
  uint8_t oldSREG = SREG;
  uint8_t bpar;
  
  bpar=parity(b);

  // stop interrupts to allow for stable baudrate
  cli();

  // Write the start bit, so pull signal HIGH
  digitalWrite(tipctx,HIGH);
  // keep it
  _delay_loop_2(tx_delay);

  // then write each of the 8 bits (reverse order)
  for (uint8_t i = 8; i > 0; --i)
  {
    if (b & 1)
      digitalWrite(tipctx,LOW);
    else
      digitalWrite(tipctx,HIGH);   
    _delay_loop_2(tx_delay);
    b >>= 1;
  }
  // parity bit 
  if (bpar & 1) 
     digitalWrite(tipctx,LOW);
  else
     digitalWrite(tipctx,HIGH);
  _delay_loop_2(tx_delay);

  // back to idle
  digitalWrite(tipctx,LOW);
  _delay_loop_2(tx_delay);
    
  // and done, re-enable interrupts
  SREG = oldSREG; 
        
}


//////////
// SETUP  
//////////

void setup() {

  // the debug console (optional)
  Serial.begin(115200);
  while (!Serial) {
    ; 
  }
  
  // the LEDs (optional)
  pinMode(ledgreen, OUTPUT);
  digitalWrite(ledgreen,HIGH);
  pinMode(ledyellow, OUTPUT);  
  digitalWrite(ledyellow,HIGH);  

  // the PS2 keyboard connector
  pinMode(kbdirq, INPUT);
  pinMode(kbddata, INPUT);
  // clear our buffer
  kbdtail=0;
  kbdhead=0;
  // enable PS2 keyboard, trigger on HIGH->LOW
  attachInterrupt(digitalPinToInterrupt(kbdirq), kbdin_interrupt, FALLING);

  // timings based on SoftwareSerial for gcc 4.8, adjusted to TIPC 2440/305 baud rx/tx
  tx_bit_delay = (F_CPU / 2440) / 4;
  rx_bit_delay = (F_CPU / 305) / 4; 
  tx_delay = subtract_cap(tx_bit_delay, 15 / 4);
  rx_delay_centering = subtract_cap(rx_bit_delay / 2, (4 + 4 + 75 + 17 - 23) / 4);
  rx_delay_intrabit = subtract_cap(rx_bit_delay, 23 / 4);
  rx_delay_stopbit = subtract_cap(rx_bit_delay * 3 / 4, (37 + 11) / 4);
      
  // the TIPC RX/TX connector (loopback signal is handled in hardware (wire))
  pinMode(tipcrx,INPUT);
  digitalWrite(tipcrx,LOW);
  pinMode(tipctx,OUTPUT);
  digitalWrite(tipctx,LOW);
  // enable TIPC command receiving interrupt, inverted UART triggers on LOW->HIGH
  attachInterrupt(digitalPinToInterrupt(tipcrx), tipcrx_interrupt, RISING);

  // time to settle things
  delay(500);
  // turn off LEDs
  digitalWrite(ledgreen,LOW);
  digitalWrite(ledyellow,LOW);
  
  // send OK to debug interface
  Serial.println("Init done");

}

//////////////// 
// WORKER LOOP
////////////////

void loop() 
{
             
    keyin = get_scan_code();    // get the raw scan code, prepare do a byte-wise marble run

    if (keyin) {                // if we got something, enter the magic state machine
      /* Serial.print("   got scan code: 0x");  // debug output
      Serial.print(keyin, HEX);
      Serial.print(", ");
      Serial.println(keyin,DEC); */
      if (keypause>0)           // did we see the pause key prefix earlier?
      {
         if (keyin==brkcode[keypause]) // use index to deal with that special case
         {
            keypause++;         // hit, so set index to next
            if (keypause == 7)  // we got a full Break key sequence
            {
              sendkey=100;      // code to be sent
            }
         } else
         { 
           keypause=0;          // weird, looked like Break, but wasn't - so reset
         }                  
      } else 
      {
      switch (keyin) {
        case 0xaa:              // obviously USB keyboard, try switching to PS2 mode
        {
          Serial.println("Reset keyboard / switch USB to PS2 mode");   // reset sequence taken from PS2KeyAdvanced library
          detachInterrupt(digitalPinToInterrupt(kbdirq));
          digitalWrite( kbddata, HIGH);
          pinMode (kbddata, OUTPUT);
          digitalWrite (kbdirq, HIGH);
          pinMode (kbdirq,OUTPUT);
          delayMicroseconds(10);
          digitalWrite(kbdirq, LOW);
          delayMicroseconds(60);
          digitalWrite(kbddata, LOW);
          pinMode(kbdirq, INPUT);
          digitalWrite(kbdirq, HIGH);
          pinMode(kbddata, INPUT);
          digitalWrite(kbddata, HIGH);
          attachInterrupt(digitalPinToInterrupt(kbdirq), kbdin_interrupt, FALLING);                
          break;
        }        
        case 0xe0:            // extended scan code, just set the flag for later
        {                   
          keyext=true;              
          break;          
        }
        case 0xe1:            // pause key prefix
        {
          if (!keypause) {
            keypause=1;
          };
          break;
        }
        case 0xf0:            // key release prefix, ack char(s) follow, so end here for now
        {
          keystop=true;          
          break;
        }                
        default:              // deal with scan code received
        {
          if (keystop) {      // are we in key release?
            keystop=false;    // yes, then reset our helper flags
            keyext=false;           
            keypause=false;
            switch (keyin)    // check for released mode byte keys first
            {
              case 0x12:      // left shift
              case 0x59:      // right shift
              {
                modebyteprev=modebyte;
                bitClear(modebyte,kbdshift);
                break;
              }              
              case 0x14:      // left ctrl (or right ctrl behind 0x0e)
              {
                modebyteprev=modebyte;
                bitClear(modebyte,kbdctrl);
                break;
              }
              case 0x11:      // left alt (or right Alt/Altgr behind 0x0e)
              {
                modebyteprev=modebyte;
                bitClear(modebyte,kbdalt);
                break;
              }
            }        
          }  else if (keyext)  // did we see an extended scan code?
          {
            keyext=false;     // yes, then reset flag
            switch (keyin)    // and map the key
            { 
              case 0x7e:      // Ctrl-Pause special effect as PS2 sequence is E0 7E
              {
                modebyteprev=0;  // always send mode byte next
                bitSet(modebyte,kbdctrl);
                sendkey=100;
                break;
              }
              case 0x14:      // right Ctrl
              {
                modebyteprev=modebyte;
                bitSet(modebyte,kbdctrl);
                break;
              }
              case 0x11:      // right Alt / Alt-Gr
              {
                modebyteprev=modebyte;
                bitSet(modebyte,kbdalt);
                break;                
              }
              default:        // extended scan code mapping
              {
                sendkey=extcodes[keyin];
              }
              
            }
          } 
          else               // ok so it's a new regular key pressed, or auto-repeat
          {
            switch (keyin)   // again, check for mode keys first   
            {
              case 0x12:     // left shift
              case 0x59:     // right shift
              {
                modebyteprev=modebyte;
                bitSet(modebyte,kbdshift);                
                break;            
              }
              case 0x14:     // left ctrl  
              {
                modebyteprev=modebyte;
                bitSet(modebyte,kbdctrl);             
                break;            
              }
              case 0x11:     // left alt
              {
                modebyteprev=modebyte;
                bitSet(modebyte,kbdalt);                
                break;
              }       
              default:       // regular scan code mapping
              {
                sendkey=scancodes[keyin];
              }
              
            }
          }
        }
      }
    }

    
    if (sendkey) {          // do we have something to send to TIPC?   
      digitalWrite(ledgreen,HIGH);
      Serial.print("Send to TIPC: ");      
      if (modebyteprev != modebyte)
      {
        Serial.print(modebyte, BIN);
        Serial.print(" ");
        tipc_send(modebyte);
        modebyteprev=modebyte;
      }     
      Serial.println(sendkey, DEC);
      tipc_send(sendkey);      
      if (sendkey == 100)   // reset all Break/Ctrl-Break/Shift-Break quirks
      {        
        modebyteprev=0;     // force mode byte again next time
        keyext=false;           
        keypause=false;
        bitClear(modebyte,kbdshift);
        bitClear(modebyte,kbdctrl);
      }
      digitalWrite(ledgreen,LOW);   
      sendkey=0;
    }
  }
      
  
    if (tipc_avail()) {     // did we receive a command from TIPC?
      digitalWrite(ledyellow,HIGH); 
      tipcchar = tipc_read();
      Serial.print("TIPC sent: ");
      Serial.println(tipcchar, DEC);
      switch (tipcchar) 
      {
        case 0x00: 
        {
          Serial.println("self-test requested");
          tipc_send(112);   // 0x70 = we are OK, thanks for asking
          break;
        }
        case 0x55: 
        {
          Serial.println("wiggle requested");  // we wiggle with hardware loopback, so just catch
          break;
        }
        default: 
        {
          Serial.print("unknown command received: ");  // huh?
          Serial.println(tipcchar, DEC);
        }
      }           
    digitalWrite(ledyellow,LOW); 
    }
     
}
  
