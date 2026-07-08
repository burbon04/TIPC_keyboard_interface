# TIPC keyboard interface/converter

The Texas Instruments Professional Computer (TIPC) came with a proprietary keyboard that has nothing in common with the IBM PC–style keyboards everyone is familiar with - except for the DIN plug, of course. Those keyboards are a little hard to come by these days, and anyone who owns a TIPC but doesn't have the keyboard knows what I'm talking about: you can't use the machine without it. That was my situation as well, so I needed a replacement.

The keyboard uses serial inverted UART communication with 2440,E,8,1 for TX and 305,E,8,1 for RX, as well as a loopback signal for keepalive testing. It is not a standalone serial terminal like, for example, the VT100, as it does not simply send ASCII codes. It also does not transmit raw scan codes like IBM keyboards do. Instead, it's something in between: it sends mode bytes to indicate the status of Ctrl, Alt, and Shift, along with key numbers that designate the pressed key.
  
Although this is quite an interesting type of keyboard, it has one major drawback: there is no way for the TIPC to detect multiple individual keys pressed at the same time. This would certainly have been a limitation for gaming—just think of Mario running (arrow key) and jumping (Ctrl or another key).
 
As always - **no warranty of any kind, use completely at your own risk**! 


Version history
- 1.0x - initial working version
- 2.00 - enhanced Alt-Gr keys support, backslash bugfix, DS1302 RTC support



## Wiring diagram
generic wiring is like this:
![wiring diagram](/docs/wiring_diagram.png)

the red bubbles connecting to the USB port:
![wiring diagram](/docs/usb_connector.png)

and the blue labels connecting to a 5 port DIN (keyboard) socket:
![wiring diagram](/docs/din_connector.png)


## RTC support

Since RTC cards tend to be damaged by leaking batteries, I added RTC support as well.
The wiring diagram for the (optional) RTC add on (DS1302) is:

![wiring diagram](/docs/rtc_addon.png)

use TIPC-KBD.EXE to read and write the RTC:

    A> tipc-kbd setrtc  
    Setting RTC to 27-02-2026 19:44:38  
    ........................................................  
    done

and

    A> tipc-kbd getrtc
    
    Requesting RTC date/time...ok
    Setting system time to 27-02-2026 19:44:53


## PCBs / KiCad files

none yet, but I think I'll design a PCB in the near future.. maybe ;)
