# TIPC keyboard interface/converter

The Texas Instruments Professional Computer (TIPC) came with a proprietary keyboard that has nothing in common with the IBM PC–style keyboards everyone is familiar with - except for the DIN plug, of course. Those keyboards are a little hard to come by these days, and anyone who owns a TIPC but doesn't have the keyboard knows what I'm talking about: you can't use the machine without it. That was my situation as well, so I needed a replacement.

The keyboard uses serial inverted UART communication with 2440,E,8,1 for TX and 305,E,8,1 for RX, as well as a loopback signal for keepalive testing. It is not a standalone serial terminal like, for example, the VT100, as it does not simply send ASCII codes. It also does not transmit raw scan codes like IBM keyboards do. Instead, it's something in between: it sends mode bytes to indicate the status of Ctrl, Alt, and Shift, along with key numbers that designate the pressed key.
  
Although this is quite an interesting type of keyboard, it has one major drawback: there is no way for the TIPC to detect multiple individual keys pressed at the same time. This would certainly have been a limitation for gaming—just think of Mario running (arrow key) and jumping (Ctrl or another key).
 
As always - **no warranty of any kind, use completely at your own risk**! 


Version history
- 1.0x - initial working version
- 2.00 - enhanced Alt-Gr keys support, backslash bugfix, DS1302 RTC support

## Prototype
![wiring diagram](/docs/prototype.png)

The Arduino acts as an converter between TIPC and a modern USB/PS2 keyboard.

No external power supply needed, the 12v provided at the TIPC's DIN port is used (regulated with an 7805).

## What's needed
- Arduino Nano (Atmel ATmega328P)
- yellow and green LED
- 10v 47µF capacitor
- 7805 voltage regulator
- 2x 680 ohm resistor
- USB 1.1/2.0 port
- 5-port DIN socket

## Supported hardware
Designed to be used with an Arduino Nano (Atmel ATmega328P).

You need to connect an USB keyboard that allows switching to the PS/2 communication protocol. Many, but not all, keyboards do - please be aware of this. Any real PS/2 (with passive PS/2->USB adapter) should work of course. 


## How To Use
Use any current Arduino IDE 1.8.15+ version to compile and flash the .ino file.
Arduino IDE 2.x should work as well but not yet tested, might require some minor timing adjustments as is uses a newer compiler toolchain.

## Limitations
Since all the timing is done in software using a single MCU, you cannot type fast as lightning. Reason for that is quite simple: PS/2 and UART timings will overlap. There are several ways to work around this, and I plan to optimize that in a later revision. But, honestly, it doesn't really bother me right now, just type at normal speed and you'll be fine ;)

## Wiring diagram

generic wiring is like this:

![wiring diagram](/docs/basic_wiring.png)

the red bubbles connecting to the USB port:

![wiring diagram](/docs/usb_connector.png)

and the blue labels connecting to a 5 port DIN (keyboard) socket:

![wiring diagram](/docs/din_connector.png)

use a 1:1 MIDI cable to connect to the TIPC.

## RTC support

Since RTC cards tend to be damaged by leaking batteries, I added RTC support as well.
The wiring diagram for the (optional) RTC add-on (DS1302) is:

![wiring diagram](/docs/rtc_addon.png)

use TIPC-KBD.EXE to set the RTC:

    A> tipc-kbd setrtc  
    Setting RTC to 27-02-2026 19:44:38  
    ........................................................  
    done

and, most importantly, set the TIPC's system time, e.g. within autoexec.bat:

    A> tipc-kbd getrtc
    
    Requesting RTC date/time...ok
    Setting system time to 27-02-2026 19:44:53


## PCBs / KiCad files

none yet, but I think I'll design a PCB in the near future.. maybe ;)
