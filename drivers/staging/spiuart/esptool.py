#!/usr/bin/env python
#
# ESP8266 & ESP32 ROM Bootloader Utility
# Copyright (C) 2014-2016 Fredrik Ahlberg, Angus Gratton, Espressif Systems (Shanghai) PTE LTD, other contributors as noted.
# https://github.com/espressif/esptool
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
# Street, Fifth Floor, Boston, MA 02110-1301 USA.

from __future__ import print_function, division

import argparse
import hashlib
import inspect
import os
import serial
import struct
import sys
import time
import base64
import zlib
import shlex

__version__ = "2.0.1"

MAX_UINT32 = 0xffffffff
MAX_UINT24 = 0xffffff

DEFAULT_TIMEOUT = 3       # timeout for most flash operations
START_FLASH_TIMEOUT = 20  # timeout for starting flash (may perform erase)
CHIP_ERASE_TIMEOUT = 120  # timeout for full chip erase
SYNC_TIMEOUT = 0.1        # timeout for syncing with bootloader


DETECTED_FLASH_SIZES = {0x12: '256KB', 0x13: '512KB', 0x14: '1MB',
                        0x15: '2MB', 0x16: '4MB', 0x17: '8MB', 0x18: '16MB'}


def check_supported_function(func, check_func):
    """
    Decorator implementation that wraps a check around an ESPLoader
    bootloader function to check if it's supported.

    This is used to capture the multidimensional differences in
    functionality between the ESP8266 & ESP32 ROM loaders, and the
    software stub that runs on both. Not possible to do this cleanly
    via inheritance alone.
    """
    def inner(*args, **kwargs):
        obj = args[0]
        if check_func(obj):
            return func(*args, **kwargs)
        else:
            raise NotImplementedInROMError(obj, func)
    return inner


def stub_function_only(func):
    """ Attribute for a function only supported in the software stub loader """
    return check_supported_function(func, lambda o: o.IS_STUB)


def stub_and_esp32_function_only(func):
    """ Attribute for a function only supported by software stubs or ESP32 ROM """
    return check_supported_function(func, lambda o: o.IS_STUB or o.CHIP_NAME == "ESP32")


PYTHON2 = sys.version_info[0] < 3  # True if on pre-Python 3

# Function to return nth byte of a bitstring
# Different behaviour on Python 2 vs 3
if PYTHON2:
    def byte(bitstr, index):
        return ord(bitstr[index])
else:
    def byte(bitstr, index):
        return bitstr[index]


def esp8266_function_only(func):
    """ Attribute for a function only supported on ESP8266 """
    return check_supported_function(func, lambda o: o.CHIP_NAME == "ESP8266")


class ESPLoader(object):
    """ Base class providing access to ESP ROM & softtware stub bootloaders.
    Subclasses provide ESP8266 & ESP32 specific functionality.

    Don't instantiate this base class directly, either instantiate a subclass or
    call ESPLoader.detect_chip() which will interrogate the chip and return the
    appropriate subclass instance.

    """
    CHIP_NAME = "Espressif device"
    IS_STUB = False

    DEFAULT_PORT = "/dev/ttyUSB0"

    # Commands supported by ESP8266 ROM bootloader
    ESP_FLASH_BEGIN = 0x02
    ESP_FLASH_DATA  = 0x03
    ESP_FLASH_END   = 0x04
    ESP_MEM_BEGIN   = 0x05
    ESP_MEM_END     = 0x06
    ESP_MEM_DATA    = 0x07
    ESP_SYNC        = 0x08
    ESP_WRITE_REG   = 0x09
    ESP_READ_REG    = 0x0a

    # Some comands supported by ESP32 ROM bootloader (or -8266 w/ stub)
    ESP_SPI_SET_PARAMS = 0x0B
    ESP_SPI_ATTACH     = 0x0D
    ESP_CHANGE_BAUDRATE = 0x0F
    ESP_FLASH_DEFL_BEGIN = 0x10
    ESP_FLASH_DEFL_DATA  = 0x11
    ESP_FLASH_DEFL_END   = 0x12
    ESP_SPI_FLASH_MD5    = 0x13

    # Some commands supported by stub only
    ESP_ERASE_FLASH = 0xD0
    ESP_ERASE_REGION = 0xD1
    ESP_READ_FLASH = 0xD2
    ESP_RUN_USER_CODE = 0xD3

    # Maximum block sized for RAM and Flash writes, respectively.
    ESP_RAM_BLOCK   = 0x1800

    FLASH_WRITE_SIZE = 0x400

    # Default baudrate. The ROM auto-bauds, so we can use more or less whatever we want.
    ESP_ROM_BAUD    = 1500000

    # First byte of the application image
    ESP_IMAGE_MAGIC = 0xe9

    # Initial state for the checksum routine
    ESP_CHECKSUM_MAGIC = 0xef

    # Flash sector size, minimum unit of erase.
    FLASH_SECTOR_SIZE = 0x1000

    UART_DATA_REG_ADDR = 0x60000078

    # Memory addresses
    IROM_MAP_START = 0x40200000
    IROM_MAP_END = 0x40300000

    # The number of bytes in the UART response that signify command status
    STATUS_BYTES_LENGTH = 2

    def __init__(self, port=DEFAULT_PORT, baud=ESP_ROM_BAUD):
        """Base constructor for ESPLoader bootloader interaction

        Don't call this constructor, either instantiate ESP8266ROM
        or ESP32ROM, or use ESPLoader.detect_chip().

        This base class has all of the instance methods for bootloader
        functionality supported across various chips & stub
        loaders. Subclasses replace the functions they don't support
        with ones which throw NotImplementedInROMError().

        """
        if isinstance(port, serial.Serial):
            self._port = port
        else:
            self._port = serial.serial_for_url(port)
        self._slip_reader = slip_reader(self._port)
        # setting baud rate in a separate step is a workaround for
        # CH341 driver on some Linux versions (this opens at 9600 then
        # sets), shouldn't matter for other platforms/drivers. See
        # https://github.com/espressif/esptool/issues/44#issuecomment-107094446
        self._set_port_baudrate(baud)

    def _set_port_baudrate(self, baud):
        try:
            self._port.baudrate = baud
        except IOError:
            raise FatalError("Failed to set baud rate %d. The driver may not support this rate." % baud)

    @staticmethod
    def detect_chip(port=DEFAULT_PORT, baud=ESP_ROM_BAUD, connect_mode='default_reset'):
        """ Use serial access to detect the chip type.

        We use the UART's datecode register for this, it's mapped at
        the same address on ESP8266 & ESP32 so we can use one
        memory read and compare to the datecode register for each chip
        type.

        This routine automatically performs ESPLoader.connect() (passing
        connect_mode parameter) as part of querying the chip.
        """
        detect_port = ESPLoader(port, baud)
        detect_port.connect(connect_mode)
        print('Detecting chip type...', end='')
        sys.stdout.flush()
        date_reg = detect_port.read_reg(ESPLoader.UART_DATA_REG_ADDR)

        for cls in [ESP8266ROM, ESP32ROM]:
            if date_reg == cls.DATE_REG_VALUE:
                # don't connect a second time
                inst = cls(detect_port._port, baud)
                print(' %s' % inst.CHIP_NAME)
                return inst
        print('')
        raise FatalError("Unexpected UART datecode value 0x%08x. Failed to autodetect chip type." % date_reg)

    """ Read a SLIP packet from the serial port """
    def read(self):
        return next(self._slip_reader)

    """ Write bytes to the serial port while performing SLIP escaping """
    def write(self, packet):
        buf = b'\xc0' \
              + (packet.replace(b'\xdb',b'\xdb\xdd').replace(b'\xc0',b'\xdb\xdc')) \
              + b'\xc0'
        self._port.write(buf)

    """ Calculate checksum of a blob, as it is defined by the ROM """
    @staticmethod
    def checksum(data, state=ESP_CHECKSUM_MAGIC):
        for b in data:
            if type(b) is int:  # python 2/3 compat
                state ^= b
            else:
                state ^= ord(b)

        return state

    """ Send a request and read the response """
    def command(self, op=None, data=b"", chk=0, wait_response=True):
        if op is not None:
            pkt = struct.pack(b'<BBHI', 0x00, op, len(data), chk) + data
            self.write(pkt)

        if not wait_response:
            return

        # tries to get a response until that response has the
        # same operation as the request or a retries limit has
        # exceeded. This is needed for some esp8266s that
        # reply with more sync responses than expected.
        for retry in range(100):
            p = self.read()
            if len(p) < 8:
                continue
            (resp, op_ret, len_ret, val) = struct.unpack('<BBHI', p[:8])
            if resp != 1:
                continue
            data = p[8:]
            if op is None or op_ret == op:
                return val, data

        raise FatalError("Response doesn't match request")

    def check_command(self, op_description, op=None, data=b'', chk=0):
        """
        Execute a command with 'command', check the result code and throw an appropriate
        FatalError if it fails.

        Returns the "result" of a successful command.
        """
        val, data = self.command(op, data, chk)

        # things are a bit weird here, bear with us

        # the status bytes are the last 2/4 bytes in the data (depending on chip)
        if len(data) < self.STATUS_BYTES_LENGTH:
            raise FatalError("Failed to %s. Only got %d byte status response." % (op_description, len(data)))
        status_bytes = data[-self.STATUS_BYTES_LENGTH:]
        # we only care if the first one is non-zero. If it is, the second byte is a reason.
        if byte(status_bytes, 0) != 0:
            raise FatalError.WithResult('Failed to %s' % op_description, status_bytes)

        # if we had more data than just the status bytes, return it as the result
        # (this is used by the md5sum command, maybe other commands?)
        if len(data) > self.STATUS_BYTES_LENGTH:
            return data[:-self.STATUS_BYTES_LENGTH]
        else:  # otherwise, just return the 'val' field which comes from the reply header (this is used by read_reg)
            return val

    def flush_input(self):
        self._port.flushInput()
        self._slip_reader = slip_reader(self._port)

    def sync(self):
        self.command(self.ESP_SYNC, b'\x07\x07\x12\x20' + 32 * b'\x55')
        for i in range(7):
            self.command()

    def _connect_attempt(self, mode='default_reset', esp32r0_delay=False):
        """ A single connection attempt, with esp32r0 workaround options """
        # esp32r0_delay is a workaround for bugs with the most common auto reset
        # circuit and Windows, if the EN pin on the dev board does not have
        # enough capacitance.
        #
        # Newer dev boards shouldn't have this problem (higher value capacitor
        # on the EN pin), and ESP32 revision 1 can't use this workaround as it
        # relies on a silicon bug.
        #
        # Details: https://github.com/espressif/esptool/issues/136
        last_error = None

        # issue reset-to-bootloader:
        # RTS = either CH_PD/EN or nRESET (both active low = chip in reset
        # DTR = GPIO0 (active low = boot to flasher)
        #
        # DTR & RTS are active low signals,
        # ie True = pin @ 0V, False = pin @ VCC.
        if mode != 'no_reset':
            self._port.setDTR(False)  # IO0=HIGH
            self._port.setRTS(True)   # EN=LOW, chip in reset
            time.sleep(0.1)
            if esp32r0_delay:
                # Some chips are more likely to trigger the esp32r0
                # watchdog reset silicon bug if they're held with EN=LOW
                # for a longer period
                time.sleep(1.2)
            self._port.setDTR(True)   # IO0=LOW
            self._port.setRTS(False)  # EN=HIGH, chip out of reset
            if esp32r0_delay:
                # Sleep longer after reset.
                # This workaround only works on revision 0 ESP32 chips,
                # it exploits a silicon bug spurious watchdog reset.
                time.sleep(0.4)  # allow watchdog reset to occur
            time.sleep(0.05)
            self._port.setDTR(False)  # IO0=HIGH, done

        self._port.timeout = SYNC_TIMEOUT
        for _ in range(5):
            try:
                self.flush_input()
                self._port.flushOutput()
                self.sync()
                self._port.timeout = DEFAULT_TIMEOUT
                return None
            except FatalError as e:
                if esp32r0_delay:
                    print('_', end='')
                else:
                    print('.', end='')
                sys.stdout.flush()
                time.sleep(0.05)
                last_error = e
        return last_error

    def connect(self, mode='default_reset'):
        """ Try connecting repeatedly until successful, or giving up """
        print('Connecting...', end='')
        sys.stdout.flush()
        last_error = None

        try:
            for _ in range(10):
                last_error = self._connect_attempt(mode=mode, esp32r0_delay=False)
                if last_error is None:
                    return
                last_error = self._connect_attempt(mode=mode, esp32r0_delay=True)
                if last_error is None:
                    return
        finally:
            print('')  # end 'Connecting...' line
        raise FatalError('Failed to connect to %s: %s' % (self.CHIP_NAME, last_error))

    """ Read memory address in target """
    def read_reg(self, addr):
        # we don't call check_command here because read_reg() function is called
        # when detecting chip type, and the way we check for success (STATUS_BYTES_LENGTH) is different
        # for different chip types (!)
        val, data = self.command(self.ESP_READ_REG, struct.pack('<I', addr))
        if byte(data, 0) != 0:
            raise FatalError.WithResult("Failed to read register address %08x" % addr, data)
        return val

    """ Write to memory address in target """
    def write_reg(self, addr, value, mask=0xFFFFFFFF, delay_us=0):
        return self.check_command("write target memory", self.ESP_WRITE_REG,
                                  struct.pack('<IIII', addr, value, mask, delay_us))

    """ Start downloading an application image to RAM """
    def mem_begin(self, size, blocks, blocksize, offset):
        return self.check_command("enter RAM download mode", self.ESP_MEM_BEGIN,
                                  struct.pack('<IIII', size, blocks, blocksize, offset))

    """ Send a block of an image to RAM """
    def mem_block(self, data, seq):
        return self.check_command("write to target RAM", self.ESP_MEM_DATA,
                                  struct.pack('<IIII', len(data), seq, 0, 0) + data,
                                  self.checksum(data))

    """ Leave download mode and run the application """
    def mem_finish(self, entrypoint=0):
        return self.check_command("leave RAM download mode", self.ESP_MEM_END,
                                  struct.pack('<II', int(entrypoint == 0), entrypoint))

    """ Start downloading to Flash (performs an erase)

    Returns number of blocks (of size self.FLASH_WRITE_SIZE) to write.
    """
    def flash_begin(self, size, offset):
        num_blocks = (size + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE
        erase_size = self.get_erase_size(offset, size)

        self._port.timeout = START_FLASH_TIMEOUT
        t = time.time()
        self.check_command("enter Flash download mode", self.ESP_FLASH_BEGIN,
                           struct.pack('<IIII', erase_size, num_blocks, self.FLASH_WRITE_SIZE, offset))
        if size != 0 and not self.IS_STUB:
            print("Took %.2fs to erase flash block" % (time.time() - t))
        self._port.timeout = DEFAULT_TIMEOUT
        return num_blocks

    """ Write block to flash """
    def flash_block(self, data, seq):
        self.check_command("write to target Flash after seq %d" % seq,
                           self.ESP_FLASH_DATA,
                           struct.pack('<IIII', len(data), seq, 0, 0) + data,
                           self.checksum(data))

    """ Leave flash mode and run/reboot """
    def flash_finish(self, reboot=False):
        pkt = struct.pack('<I', int(not reboot))
        # stub sends a reply to this command
        self.check_command("leave Flash mode", self.ESP_FLASH_END, pkt)

    """ Run application code in flash """
    def run(self, reboot=False):
        # Fake flash begin immediately followed by flash end
        self.flash_begin(0, 0)
        self.flash_finish(reboot)

    """ Read SPI flash manufacturer and device id """
    def flash_id(self):
        SPIFLASH_RDID = 0x9F
        return self.run_spiflash_command(SPIFLASH_RDID, b"", 24)

    def parse_flash_size_arg(self, arg):
        try:
            return self.FLASH_SIZES[arg]
        except KeyError:
            raise FatalError("Flash size '%s' is not supported by this chip type. Supported sizes: %s"
                             % (arg, ", ".join(self.FLASH_SIZES.keys())))

    def run_stub(self, stub=None):
        if stub is None:
            if self.IS_STUB:
                raise FatalError("Not possible for a stub to load another stub (memory likely to overlap.)")
            stub = self.STUB_CODE

        # Upload
        print("Uploading stub...")
        for field in ['text', 'data']:
            if field in stub:
                offs = stub[field + "_start"]
                length = len(stub[field])
                blocks = (length + self.ESP_RAM_BLOCK - 1) // self.ESP_RAM_BLOCK
                self.mem_begin(length, blocks, self.ESP_RAM_BLOCK, offs)
                for seq in range(blocks):
                    from_offs = seq * self.ESP_RAM_BLOCK
                    to_offs = from_offs + self.ESP_RAM_BLOCK
                    self.mem_block(stub[field][from_offs:to_offs], seq)
        print("Running stub...")
        self.mem_finish(stub['entry'])

        p = self.read()
        if p != b'OHAI':
            raise FatalError("Failed to start stub. Unexpected response: %s" % p)
        print("Stub running...")
        return self.STUB_CLASS(self)

    @stub_and_esp32_function_only
    def flash_defl_begin(self, size, compsize, offset):
        """ Start downloading compressed data to Flash (performs an erase)

        Returns number of blocks (size self.FLASH_WRITE_SIZE) to write.
        """
        num_blocks = (compsize + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE
        erase_blocks = (size + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE

        self._port.timeout = START_FLASH_TIMEOUT
        t = time.time()
        if self.IS_STUB:
            write_size = size  # stub expects number of bytes here, manages erasing internally
        else:
            write_size = erase_blocks * self.FLASH_WRITE_SIZE  # ROM expects rounded up to erase block size
        print("Compressed %d bytes to %d..." % (size, compsize))
        self.check_command("enter compressed flash mode", self.ESP_FLASH_DEFL_BEGIN,
                           struct.pack('<IIII', write_size, num_blocks, self.FLASH_WRITE_SIZE, offset))
        if size != 0 and not self.IS_STUB:
            # (stub erases as it writes, but ROM loaders erase on begin)
            print("Took %.2fs to erase flash block" % (time.time() - t))
        self._port.timeout = DEFAULT_TIMEOUT
        return num_blocks

    """ Write block to flash, send compressed """
    @stub_and_esp32_function_only
    def flash_defl_block(self, data, seq):
        self.check_command("write compressed data to flash after seq %d" % seq,
                           self.ESP_FLASH_DEFL_DATA, struct.pack('<IIII', len(data), seq, 0, 0) + data, self.checksum(data))

    """ Leave compressed flash mode and run/reboot """
    @stub_and_esp32_function_only
    def flash_defl_finish(self, reboot=False):
        if not reboot and not self.IS_STUB:
            # skip sending flash_finish to ROM loader, as this
            # exits the bootloader. Stub doesn't do this.
            return
        pkt = struct.pack('<I', int(not reboot))
        self.check_command("leave compressed flash mode", self.ESP_FLASH_DEFL_END, pkt)
        self.in_bootloader = False

    @stub_and_esp32_function_only
    def flash_md5sum(self, addr, size):
        # the MD5 command returns additional bytes in the standard
        # command reply slot
        res = self.check_command('calculate md5sum', self.ESP_SPI_FLASH_MD5, struct.pack('<IIII', addr, size, 0, 0))

        if len(res) == 32:
            return res.decode("utf-8")  # already hex formatted
        elif len(res) == 16:
            return hexify(res).lower()
        else:
            raise FatalError("MD5Sum command returned unexpected result: %r" % res)

    @stub_and_esp32_function_only
    def change_baud(self, baud):
        print("Changing baud rate to %d" % baud)
        self.command(self.ESP_CHANGE_BAUDRATE, struct.pack('<II', baud, 0))
        print("Changed.")
        self._set_port_baudrate(baud)
        time.sleep(0.05)  # get rid of crap sent during baud rate change
        self.flush_input()

    @stub_function_only
    def erase_flash(self):
        # depending on flash chip model the erase may take this long (maybe longer!)
        self._port.timeout = CHIP_ERASE_TIMEOUT
        try:
            self.check_command("erase flash", self.ESP_ERASE_FLASH)
        finally:
            self._port.timeout = DEFAULT_TIMEOUT

    @stub_function_only
    def erase_region(self, offset, size):
        if offset % self.FLASH_SECTOR_SIZE != 0:
            raise FatalError("Offset to erase from must be a multiple of 4096")
        if size % self.FLASH_SECTOR_SIZE != 0:
            raise FatalError("Size of data to erase must be a multiple of 4096")
        self.check_command("erase region", self.ESP_ERASE_REGION, struct.pack('<II', offset, size))

    @stub_function_only
    def read_flash(self, offset, length, progress_fn=None):
        # issue a standard bootloader command to trigger the read
        self.check_command("read flash", self.ESP_READ_FLASH,
                           struct.pack('<IIII',
                                       offset,
                                       length,
                                       self.FLASH_SECTOR_SIZE,
                                       64))
        # now we expect (length // block_size) SLIP frames with the data
        data = b''
        while len(data) < length:
            p = self.read()
            data += p
            self.write(struct.pack('<I', len(data)))
            if progress_fn and (len(data) % 1024 == 0 or len(data) == length):
                progress_fn(len(data), length)
        if progress_fn:
            progress_fn(len(data), length)
        if len(data) > length:
            raise FatalError('Read more than expected')
        digest_frame = self.read()
        if len(digest_frame) != 16:
            raise FatalError('Expected digest, got: %s' % hexify(digest_frame))
        expected_digest = hexify(digest_frame).upper()
        digest = hashlib.md5(data).hexdigest().upper()
        if digest != expected_digest:
            raise FatalError('Digest mismatch: expected %s, got %s' % (expected_digest, digest))
        return data

    def flash_spi_attach(self, hspi_arg):
        """Send SPI attach command to enable the SPI flash pins

        ESP8266 ROM does this when you send flash_begin, ESP32 ROM
        has it as a SPI command.
        """
        # last 3 bytes in ESP_SPI_ATTACH argument are reserved values
        arg = struct.pack('<I', hspi_arg)
        if not self.IS_STUB:
            # ESP32 ROM loader takes additional 'is legacy' arg, which is not
            # currently supported in the stub loader or esptool.py (as it's not usually needed.)
            is_legacy = 0
            arg += struct.pack('BBBB', is_legacy, 0, 0, 0)
        self.check_command("configure SPI flash pins", ESP32ROM.ESP_SPI_ATTACH, arg)

    def flash_set_parameters(self, size):
        """Tell the ESP bootloader the parameters of the chip

        Corresponds to the "flashchip" data structure that the ROM
        has in RAM.

        'size' is in bytes.

        All other flash parameters are currently hardcoded (on ESP8266
        these are mostly ignored by ROM code, on ESP32 I'm not sure.)
        """
        fl_id = 0
        total_size = size
        block_size = 64 * 1024
        sector_size = 4 * 1024
        page_size = 256
        status_mask = 0xffff
        self.check_command("set SPI params", ESP32ROM.ESP_SPI_SET_PARAMS,
                           struct.pack('<IIIIII', fl_id, total_size, block_size, sector_size, page_size, status_mask))

    def run_spiflash_command(self, spiflash_command, data=b"", read_bits=0):
        """Run an arbitrary SPI flash command.

        This function uses the "USR_COMMAND" functionality in the ESP
        SPI hardware, rather than the precanned commands supported by
        hardware. So the value of spiflash_command is an actual command
        byte, sent over the wire.

        After writing command byte, writes 'data' to MOSI and then
        reads back 'read_bits' of reply on MISO. Result is a number.
        """

        # SPI_USR register flags
        SPI_USR_COMMAND = (1 << 31)
        SPI_USR_MISO    = (1 << 28)
        SPI_USR_MOSI    = (1 << 27)

        # SPI registers, base address differs ESP32 vs 8266
        base = self.SPI_REG_BASE
        SPI_CMD_REG       = base + 0x00
        SPI_USR_REG       = base + 0x1C
        SPI_USR1_REG      = base + 0x20
        SPI_USR2_REG      = base + 0x24
        SPI_W0_REG        = base + self.SPI_W0_OFFS

        # following two registers are ESP32 only
        if self.SPI_HAS_MOSI_DLEN_REG:
            # ESP32 has a more sophisticated wayto set up "user" commands
            def set_data_lengths(mosi_bits, miso_bits):
                SPI_MOSI_DLEN_REG = base + 0x28
                SPI_MISO_DLEN_REG = base + 0x2C
                if mosi_bits > 0:
                    self.write_reg(SPI_MOSI_DLEN_REG, mosi_bits - 1)
                if miso_bits > 0:
                    self.write_reg(SPI_MISO_DLEN_REG, miso_bits - 1)
        else:

            def set_data_lengths(mosi_bits, miso_bits):
                SPI_DATA_LEN_REG = SPI_USR1_REG
                SPI_MOSI_BITLEN_S = 17
                SPI_MISO_BITLEN_S = 8
                mosi_mask = 0 if (mosi_bits == 0) else (mosi_bits - 1)
                miso_mask = 0 if (miso_bits == 0) else (miso_bits - 1)
                self.write_reg(SPI_DATA_LEN_REG,
                               (miso_mask << SPI_MISO_BITLEN_S) | (
                                   mosi_mask << SPI_MOSI_BITLEN_S))

        # SPI peripheral "command" bitmasks for SPI_CMD_REG
        SPI_CMD_USR  = (1 << 18)

        # shift values
        SPI_USR2_DLEN_SHIFT = 28

        if read_bits > 32:
            raise FatalError("Reading more than 32 bits back from a SPI flash operation is unsupported")
        if len(data) > 64:
            raise FatalError("Writing more than 64 bytes of data with one SPI command is unsupported")

        data_bits = len(data) * 8
        old_spi_usr = self.read_reg(SPI_USR_REG)
        old_spi_usr2 = self.read_reg(SPI_USR2_REG)
        flags = SPI_USR_COMMAND
        if read_bits > 0:
            flags |= SPI_USR_MISO
        if data_bits > 0:
            flags |= SPI_USR_MOSI
        set_data_lengths(data_bits, read_bits)
        self.write_reg(SPI_USR_REG, flags)
        self.write_reg(SPI_USR2_REG,
                       (7 << SPI_USR2_DLEN_SHIFT) | spiflash_command)
        if data_bits == 0:
            self.write_reg(SPI_W0_REG, 0)  # clear data register before we read it
        else:
            data = pad_to(data, 4, b'\00')  # pad to 32-bit multiple
            words = struct.unpack("I" * (len(data) // 4), data)
            next_reg = SPI_W0_REG
            for word in words:
                self.write_reg(next_reg, word)
                next_reg += 4
        self.write_reg(SPI_CMD_REG, SPI_CMD_USR)

        def wait_done():
            for _ in range(10):
                if (self.read_reg(SPI_CMD_REG) & SPI_CMD_USR) == 0:
                    return
            raise FatalError("SPI command did not complete in time")
        wait_done()

        status = self.read_reg(SPI_W0_REG)
        # restore some SPI controller registers
        self.write_reg(SPI_USR_REG, old_spi_usr)
        self.write_reg(SPI_USR2_REG, old_spi_usr2)
        return status

    def read_status(self, num_bytes=2):
        """Read up to 24 bits (num_bytes) of SPI flash status register contents
        via RDSR, RDSR2, RDSR3 commands

        Not all SPI flash supports all three commands. The upper 1 or 2
        bytes may be 0xFF.
        """
        SPIFLASH_RDSR  = 0x05
        SPIFLASH_RDSR2 = 0x35
        SPIFLASH_RDSR3 = 0x15

        status = 0
        shift = 0
        for cmd in [SPIFLASH_RDSR, SPIFLASH_RDSR2, SPIFLASH_RDSR3][0:num_bytes]:
            status += self.run_spiflash_command(cmd, read_bits=8) << shift
            shift += 8
        return status

    def write_status(self, new_status, num_bytes=2, set_non_volatile=False):
        """Write up to 24 bits (num_bytes) of new status register

        num_bytes can be 1, 2 or 3.

        Not all flash supports the additional commands to write the
        second and third byte of the status register. When writing 2
        bytes, esptool also sends a 16-byte WRSR command (as some
        flash types use this instead of WRSR2.)

        If the set_non_volatile flag is set, non-volatile bits will
        be set as well as volatile ones (WREN used instead of WEVSR).

        """
        SPIFLASH_WRSR = 0x01
        SPIFLASH_WRSR2 = 0x31
        SPIFLASH_WRSR3 = 0x11
        SPIFLASH_WEVSR = 0x50
        SPIFLASH_WREN = 0x06
        SPIFLASH_WRDI = 0x04

        enable_cmd = SPIFLASH_WREN if set_non_volatile else SPIFLASH_WEVSR

        # try using a 16-bit WRSR (not supported by all chips)
        # this may be redundant, but shouldn't hurt
        if num_bytes == 2:
            self.run_spiflash_command(enable_cmd)
            self.run_spiflash_command(SPIFLASH_WRSR, struct.pack("<H", new_status))

        # also try using individual commands (also not supported by all chips for num_bytes 2 & 3)
        for cmd in [SPIFLASH_WRSR, SPIFLASH_WRSR2, SPIFLASH_WRSR3][0:num_bytes]:
            self.run_spiflash_command(enable_cmd)
            self.run_spiflash_command(cmd, struct.pack("B", new_status & 0xFF))
            new_status >>= 8

        self.run_spiflash_command(SPIFLASH_WRDI)

    def hard_reset(self):
        self._port.setRTS(True)  # EN->LOW
        time.sleep(0.1)
        self._port.setRTS(False)

    def soft_reset(self, stay_in_bootloader):
        if not self.IS_STUB:
            if stay_in_bootloader:
                return  # ROM bootloader is already in bootloader!
            else:
                # 'run user code' is as close to a soft reset as we can do
                self.flash_begin(0, 0)
                self.flash_finish(False)
        else:
            if stay_in_bootloader:
                # soft resetting from the stub loader
                # will re-load the ROM bootloader
                self.flash_begin(0, 0)
                self.flash_finish(True)
            elif self.CHIP_NAME != "ESP8266":
                raise FatalError("Soft resetting is currently only supported on ESP8266")
            else:
                # running user code from stub loader requires some hacks
                # in the stub loader
                self.command(self.ESP_RUN_USER_CODE, wait_response=False)


class ESP8266ROM(ESPLoader):
    """ Access class for ESP8266 ROM bootloader
    """
    CHIP_NAME = "ESP8266"
    IS_STUB = False

    DATE_REG_VALUE = 0x00062000

    # OTP ROM addresses
    ESP_OTP_MAC0    = 0x3ff00050
    ESP_OTP_MAC1    = 0x3ff00054
    ESP_OTP_MAC3    = 0x3ff0005c

    SPI_REG_BASE    = 0x60000200
    SPI_W0_OFFS     = 0x40
    SPI_HAS_MOSI_DLEN_REG = False

    FLASH_SIZES = {
        '512KB':0x00,
        '256KB':0x10,
        '1MB':0x20,
        '2MB':0x30,
        '4MB':0x40,
        '2MB-c1': 0x50,
        '4MB-c1':0x60,
        '8MB':0x80,
        '16MB':0x90,
    }

    BOOTLOADER_FLASH_OFFSET = 0

    def get_chip_description(self):
        return "ESP8266"

    def flash_spi_attach(self, hspi_arg):
        if self.IS_STUB:
            super(ESP8266ROM, self).flash_spi_attach(hspi_arg)
        else:
            # ESP8266 ROM has no flash_spi_attach command in serial protocol,
            # but flash_begin will do it
            self.flash_begin(0, 0)

    def flash_set_parameters(self, size):
        # not implemented in ROM, but OK to silently skip for ROM
        if self.IS_STUB:
            super(ESP8266ROM, self).flash_set_parameters(size)

    def chip_id(self):
        """ Read Chip ID from OTP ROM - see http://esp8266-re.foogod.com/wiki/System_get_chip_id_%28IoT_RTOS_SDK_0.9.9%29 """
        id0 = self.read_reg(self.ESP_OTP_MAC0)
        id1 = self.read_reg(self.ESP_OTP_MAC1)
        return (id0 >> 24) | ((id1 & MAX_UINT24) << 8)

    def read_mac(self):
        """ Read MAC from OTP ROM """
        mac0 = self.read_reg(self.ESP_OTP_MAC0)
        mac1 = self.read_reg(self.ESP_OTP_MAC1)
        mac3 = self.read_reg(self.ESP_OTP_MAC3)
        if (mac3 != 0):
            oui = ((mac3 >> 16) & 0xff, (mac3 >> 8) & 0xff, mac3 & 0xff)
        elif ((mac1 >> 16) & 0xff) == 0:
            oui = (0x18, 0xfe, 0x34)
        elif ((mac1 >> 16) & 0xff) == 1:
            oui = (0xac, 0xd0, 0x74)
        else:
            raise FatalError("Unknown OUI")
        return oui + ((mac1 >> 8) & 0xff, mac1 & 0xff, (mac0 >> 24) & 0xff)

    def get_erase_size(self, offset, size):
        """ Calculate an erase size given a specific size in bytes.

        Provides a workaround for the bootloader erase bug."""

        sectors_per_block = 16
        sector_size = self.FLASH_SECTOR_SIZE
        num_sectors = (size + sector_size - 1) // sector_size
        start_sector = offset // sector_size

        head_sectors = sectors_per_block - (start_sector % sectors_per_block)
        if num_sectors < head_sectors:
            head_sectors = num_sectors

        if num_sectors < 2 * head_sectors:
            return (num_sectors + 1) // 2 * sector_size
        else:
            return (num_sectors - head_sectors) * sector_size


class ESP8266StubLoader(ESP8266ROM):
    """ Access class for ESP8266 stub loader, runs on top of ROM.
    """
    FLASH_WRITE_SIZE = 0x400  # matches MAX_WRITE_BLOCK in stub_loader.c
    IS_STUB = True

    def __init__(self, rom_loader):
        self._port = rom_loader._port
        self.flush_input()  # resets _slip_reader

    def get_erase_size(self, offset, size):
        return size  # stub doesn't have same size bug as ROM loader


ESP8266ROM.STUB_CLASS = ESP8266StubLoader


class ESP32ROM(ESPLoader):
    """Access class for ESP32 ROM bootloader

    """
    CHIP_NAME = "ESP32"
    IS_STUB = False

    DATE_REG_VALUE = 0x15122500

    IROM_MAP_START = 0x400d0000
    IROM_MAP_END   = 0x40400000
    DROM_MAP_START = 0x3F400000
    DROM_MAP_END   = 0x3F700000

    # ESP32 uses a 4 byte status reply
    STATUS_BYTES_LENGTH = 4

    SPI_REG_BASE   = 0x60002000
    EFUSE_REG_BASE = 0x6001a000

    SPI_W0_OFFS = 0x80
    SPI_HAS_MOSI_DLEN_REG = True

    FLASH_SIZES = {
        '1MB':0x00,
        '2MB':0x10,
        '4MB':0x20,
        '8MB':0x30,
        '16MB':0x40
    }

    BOOTLOADER_FLASH_OFFSET = 0x1000

    def get_chip_description(self):
        blk3 = self.read_efuse(3)
        chip_version = (blk3 >> 12) & 0xF
        pkg_version = (blk3 >> 9) & 0x07

        silicon_rev = {
            0: "0",
            8: "1"
        }.get(chip_version, "(unknown 0x%x)" % chip_version)

        chip_name = {
            0: "ESP32D0WDQ6",
            1: "ESP32D0WDQ5",
            2: "ESP32D2WDQ5",
        }.get(pkg_version, "unknown ESP32")

        return "%s (revision %s)" % (chip_name, silicon_rev)

    def read_efuse(self, n):
        """ Read the nth word of the ESP3x EFUSE region. """
        return self.read_reg(self.EFUSE_REG_BASE + (4 * n))

    def chip_id(self):
        word16 = self.read_efuse(1)
        word17 = self.read_efuse(2)
        return ((word17 & MAX_UINT24) << 24) | (word16 >> 8) & MAX_UINT24

    def read_mac(self):
        """ Read MAC from EFUSE region """
        words = [self.read_efuse(2), self.read_efuse(1)]
        bitstring = struct.pack(">II", *words)
        bitstring = bitstring[2:8]  # trim the 2 byte CRC
        try:
            return tuple(ord(b) for b in bitstring)
        except TypeError:  # Python 3, bitstring elements are already bytes
            return tuple(bitstring)

    def get_erase_size(self, offset, size):
        return size


class ESP32StubLoader(ESP32ROM):
    """ Access class for ESP32 stub loader, runs on top of ROM.
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    STATUS_BYTES_LENGTH = 2  # same as ESP8266, different to ESP32 ROM
    IS_STUB = True

    def __init__(self, rom_loader):
        self._port = rom_loader._port
        self.flush_input()  # resets _slip_reader


ESP32ROM.STUB_CLASS = ESP32StubLoader


class ESPBOOTLOADER(object):
    """ These are constants related to software ESP bootloader, working with 'v2' image files """

    # First byte of the "v2" application image
    IMAGE_V2_MAGIC = 0xea

    # First 'segment' value in a "v2" application image, appears to be a constant version value?
    IMAGE_V2_SEGMENT = 4


def LoadFirmwareImage(chip, filename):
    """ Load a firmware image. Can be for ESP8266 or ESP32. ESP8266 images will be examined to determine if they are
        original ROM firmware images (ESPFirmwareImage) or "v2" OTA bootloader images.

        Returns a BaseFirmwareImage subclass, either ESPFirmwareImage (v1) or OTAFirmwareImage (v2).
    """
    with open(filename, 'rb') as f:
        if chip == 'esp32':
            return ESP32FirmwareImage(f)
        else:  # Otherwise, ESP8266 so look at magic to determine the image type
            magic = ord(f.read(1))
            f.seek(0)
            if magic == ESPLoader.ESP_IMAGE_MAGIC:
                return ESPFirmwareImage(f)
            elif magic == ESPBOOTLOADER.IMAGE_V2_MAGIC:
                return OTAFirmwareImage(f)
            else:
                raise FatalError("Invalid image magic number: %d" % magic)


class ImageSegment(object):
    """ Wrapper class for a segment in an ESP image
    (very similar to a section in an ELFImage also) """
    def __init__(self, addr, data, file_offs=None):
        self.addr = addr
        # pad all ImageSegments to at least 4 bytes length
        self.data = pad_to(data, 4, b'\x00')
        self.file_offs = file_offs
        self.include_in_checksum = True

    def copy_with_new_addr(self, new_addr):
        """ Return a new ImageSegment with same data, but mapped at
        a new address. """
        return ImageSegment(new_addr, self.data, 0)

    def __repr__(self):
        r = "len 0x%05x load 0x%08x" % (len(self.data), self.addr)
        if self.file_offs is not None:
            r += " file_offs 0x%08x" % (self.file_offs)
        return r


class ELFSection(ImageSegment):
    """ Wrapper class for a section in an ELF image, has a section
    name as well as the common properties of an ImageSegment. """
    def __init__(self, name, addr, data):
        super(ELFSection, self).__init__(addr, data)
        self.name = name.decode("utf-8")

    def __repr__(self):
        return "%s %s" % (self.name, super(ELFSection, self).__repr__())


class BaseFirmwareImage(object):
    SEG_HEADER_LEN = 8

    """ Base class with common firmware image functions """
    def __init__(self):
        self.segments = []
        self.entrypoint = 0

    def load_common_header(self, load_file, expected_magic):
            (magic, segments, self.flash_mode, self.flash_size_freq, self.entrypoint) = struct.unpack('<BBBBI', load_file.read(8))

            if magic != expected_magic or segments > 16:
                raise FatalError('Invalid firmware image magic=%d segments=%d' % (magic, segments))
            return segments

    def load_segment(self, f, is_irom_segment=False):
        """ Load the next segment from the image file """
        file_offs = f.tell()
        (offset, size) = struct.unpack('<II', f.read(8))
        self.warn_if_unusual_segment(offset, size, is_irom_segment)
        segment_data = f.read(size)
        if len(segment_data) < size:
            raise FatalError('End of file reading segment 0x%x, length %d (actual length %d)' % (offset, size, len(segment_data)))
        segment = ImageSegment(offset, segment_data, file_offs)
        self.segments.append(segment)
        return segment

    def warn_if_unusual_segment(self, offset, size, is_irom_segment):
        if not is_irom_segment:
            if offset > 0x40200000 or offset < 0x3ffe0000 or size > 65536:
                print('WARNING: Suspicious segment 0x%x, length %d' % (offset, size))

    def save_segment(self, f, segment, checksum=None):
        """ Save the next segment to the image file, return next checksum value if provided """
        f.write(struct.pack('<II', segment.addr, len(segment.data)))
        f.write(segment.data)
        if checksum is not None:
            return ESPLoader.checksum(segment.data, checksum)

    def read_checksum(self, f):
        """ Return ESPLoader checksum from end of just-read image """
        # Skip the padding. The checksum is stored in the last byte so that the
        # file is a multiple of 16 bytes.
        align_file_position(f, 16)
        return ord(f.read(1))

    def calculate_checksum(self):
        """ Calculate checksum of loaded image, based on segments in
        segment array.
        """
        checksum = ESPLoader.ESP_CHECKSUM_MAGIC
        for seg in self.segments:
            if seg.include_in_checksum:
                checksum = ESPLoader.checksum(seg.data, checksum)
        return checksum

    def append_checksum(self, f, checksum):
        """ Append ESPLoader checksum to the just-written image """
        align_file_position(f, 16)
        f.write(struct.pack(b'B', checksum))

    def write_common_header(self, f, segments):
        f.write(struct.pack('<BBBBI', ESPLoader.ESP_IMAGE_MAGIC, len(segments),
                            self.flash_mode, self.flash_size_freq, self.entrypoint))

    def is_irom_addr(self, addr):
        """ Returns True if an address starts in the irom region.
        Valid for ESP8266 only.
        """
        return ESP8266ROM.IROM_MAP_START <= addr < ESP8266ROM.IROM_MAP_END

    def get_irom_segment(self):
            irom_segments = [s for s in self.segments if self.is_irom_addr(s.addr)]
            if len(irom_segments) > 0:
                if len(irom_segments) != 1:
                    raise FatalError('Found %d segments that could be irom0. Bad ELF file?' % len(irom_segments))
                return irom_segments[0]
            return None

    def get_non_irom_segments(self):
        irom_segment = self.get_irom_segment()
        return [s for s in self.segments if s != irom_segment]


class ESPFirmwareImage(BaseFirmwareImage):
    """ 'Version 1' firmware image, segments loaded directly by the ROM bootloader. """

    ROM_LOADER = ESP8266ROM

    def __init__(self, load_file=None):
        super(ESPFirmwareImage, self).__init__()
        self.flash_mode = 0
        self.flash_size_freq = 0
        self.version = 1

        if load_file is not None:
            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)

            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        return input_file + '-'

    def save(self, basename):
        """ Save a set of V1 images for flashing. Parameter is a base filename. """
        # IROM data goes in its own plain binary file
        irom_segment = self.get_irom_segment()
        if irom_segment is not None:
            with open("%s0x%05x.bin" % (basename, irom_segment.addr - ESP8266ROM.IROM_MAP_START), "wb") as f:
                f.write(irom_segment.data)

        # everything but IROM goes at 0x00000 in an image file
        normal_segments = self.get_non_irom_segments()
        with open("%s0x00000.bin" % basename, 'wb') as f:
            self.write_common_header(f, normal_segments)
            checksum = ESPLoader.ESP_CHECKSUM_MAGIC
            for segment in normal_segments:
                checksum = self.save_segment(f, segment, checksum)
            self.append_checksum(f, checksum)


class OTAFirmwareImage(BaseFirmwareImage):
    """ 'Version 2' firmware image, segments loaded by software bootloader stub
        (ie Espressif bootloader or rboot)
    """

    ROM_LOADER = ESP8266ROM

    def __init__(self, load_file=None):
        super(OTAFirmwareImage, self).__init__()
        self.version = 2
        if load_file is not None:
            segments = self.load_common_header(load_file, ESPBOOTLOADER.IMAGE_V2_MAGIC)
            if segments != ESPBOOTLOADER.IMAGE_V2_SEGMENT:
                # segment count is not really segment count here, but we expect to see '4'
                print('Warning: V2 header has unexpected "segment" count %d (usually 4)' % segments)

            # irom segment comes before the second header
            #
            # the file is saved in the image with a zero load address
            # in the header, so we need to calculate a load address
            irom_segment = self.load_segment(load_file, True)
            # for actual mapped addr, add ESP8266ROM.IROM_MAP_START + flashing_Addr + 8
            irom_segment.addr = 0
            irom_segment.include_in_checksum = False

            first_flash_mode = self.flash_mode
            first_flash_size_freq = self.flash_size_freq
            first_entrypoint = self.entrypoint
            # load the second header

            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)

            if first_flash_mode != self.flash_mode:
                print('WARNING: Flash mode value in first header (0x%02x) disagrees with second (0x%02x). Using second value.'
                      % (first_flash_mode, self.flash_mode))
            if first_flash_size_freq != self.flash_size_freq:
                print('WARNING: Flash size/freq value in first header (0x%02x) disagrees with second (0x%02x). Using second value.'
                      % (first_flash_size_freq, self.flash_size_freq))
            if first_entrypoint != self.entrypoint:
                print('WARNING: Entrypoint address in first header (0x%08x) disagrees with second header (0x%08x). Using second value.'
                      % (first_entrypoint, self.entrypoint))

            # load all the usual segments
            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        irom_segment = self.get_irom_segment()
        if irom_segment is not None:
            irom_offs = irom_segment.addr - ESP8266ROM.IROM_MAP_START
        else:
            irom_offs = 0
        return "%s-0x%05x.bin" % (os.path.splitext(input_file)[0],
                                  irom_offs & ~(ESPLoader.FLASH_SECTOR_SIZE - 1))

    def save(self, filename):
        with open(filename, 'wb') as f:
            # Save first header for irom0 segment
            f.write(struct.pack(b'<BBBBI', ESPBOOTLOADER.IMAGE_V2_MAGIC, ESPBOOTLOADER.IMAGE_V2_SEGMENT,
                                self.flash_mode, self.flash_size_freq, self.entrypoint))

            irom_segment = self.get_irom_segment()
            if irom_segment is not None:
                # save irom0 segment, make sure it has load addr 0 in the file
                irom_segment = irom_segment.copy_with_new_addr(0)
                self.save_segment(f, irom_segment)

            # second header, matches V1 header and contains loadable segments
            normal_segments = self.get_non_irom_segments()
            self.write_common_header(f, normal_segments)
            checksum = ESPLoader.ESP_CHECKSUM_MAGIC
            for segment in normal_segments:
                checksum = self.save_segment(f, segment, checksum)
            self.append_checksum(f, checksum)


class ESP32FirmwareImage(BaseFirmwareImage):
    """ ESP32 firmware image is very similar to V1 ESP8266 image,
    except with an additional 16 byte reserved header at top of image,
    and because of new flash mapping capabilities the flash-mapped regions
    can be placed in the normal image (just @ 64kB padded offsets).
    """

    ROM_LOADER = ESP32ROM

    # 16 byte extended header contains WP pin number (byte), then 6 half-byte drive stength
    # config fields, then 12 reserved bytes. None of this is exposed in esptool.py right now,
    # but we need to set WP to 0xEE (disabled) to avoid problems when remapping SPI flash
    # pins via efuse (for example on ESP32-D2WD).
    EXTENDED_HEADER = [0xEE] + ([0] * 15)
    EXTENDED_HEADER_STRUCT_FMT = "B" * 16

    def __init__(self, load_file=None):
        super(ESP32FirmwareImage, self).__init__()
        self.flash_mode = 0
        self.flash_size_freq = 0
        self.version = 1

        if load_file is not None:
            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)
            additional_header = list(struct.unpack(self.EXTENDED_HEADER_STRUCT_FMT, load_file.read(16)))

            # check these bytes are unused
            if additional_header != self.EXTENDED_HEADER:
                print("WARNING: ESP32 image header contains unknown flags. Possibly this image is from a different version of esptool.py")

            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

    def is_flash_addr(self, addr):
        return (ESP32ROM.IROM_MAP_START <= addr < ESP32ROM.IROM_MAP_END) \
            or (ESP32ROM.DROM_MAP_START <= addr < ESP32ROM.DROM_MAP_END)

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        return "%s.bin" % (os.path.splitext(input_file)[0])

    def warn_if_unusual_segment(self, offset, size, is_irom_segment):
        pass  # TODO: add warnings for ESP32 segment offset/size combinations that are wrong

    def save(self, filename):
        padding_segments = 0
        with open(filename, 'wb') as f:
            self.write_common_header(f, self.segments)

            # first 4 bytes of header are read by ROM bootloader for SPI
            # config, but currently unused
            f.write(struct.pack(self.EXTENDED_HEADER_STRUCT_FMT, *self.EXTENDED_HEADER))

            checksum = ESPLoader.ESP_CHECKSUM_MAGIC
            last_addr = None
            for segment in sorted(self.segments, key=lambda s:s.addr):
                # IROM/DROM segment flash mappings need to align on
                # 64kB boundaries.
                #
                # TODO: intelligently order segments to reduce wastage
                # by squeezing smaller DRAM/IRAM segments into the
                # 64kB padding space.
                IROM_ALIGN = 65536

                # check for multiple ELF sections that live in the same flash mapping region.
                # this is usually a sign of a broken linker script, but if you have a legitimate
                # use case then let us know (we can merge segments here, but as a rule you probably
                # want to merge them in your linker script.)
                if last_addr is not None and self.is_flash_addr(last_addr) \
                   and self.is_flash_addr(segment.addr) and segment.addr // IROM_ALIGN == last_addr // IROM_ALIGN:
                    raise FatalError(("Segment loaded at 0x%08x lands in same 64KB flash mapping as segment loaded at 0x%08x. " +
                                     "Can't generate binary. Suggest changing linker script or ELF to merge sections.") %
                                     (segment.addr, last_addr))
                last_addr = segment.addr

                if self.is_flash_addr(segment.addr):
                    # Actual alignment required for the segment header: positioned so that
                    # after we write the next 8 byte header, file_offs % IROM_ALIGN == segment.addr % IROM_ALIGN
                    #
                    # (this is because the segment's vaddr may not be IROM_ALIGNed, more likely is aligned
                    # IROM_ALIGN+0x10 to account for longest possible header.
                    align_past = (segment.addr % IROM_ALIGN) - self.SEG_HEADER_LEN
                    assert (align_past + self.SEG_HEADER_LEN) == (segment.addr % IROM_ALIGN)

                    # subtract SEG_HEADER_LEN a second time, as the padding block has a header as well
                    pad_len = (IROM_ALIGN - (f.tell() % IROM_ALIGN)) + align_past - self.SEG_HEADER_LEN
                    if pad_len < 0:
                        pad_len += IROM_ALIGN
                    if pad_len > 0:
                        null = ImageSegment(0, b'\x00' * pad_len, f.tell())
                        checksum = self.save_segment(f, null, checksum)
                        padding_segments += 1
                    # verify that after the 8 byte header is added, were are at the correct offset relative to the segment's vaddr
                    assert (f.tell() + 8) % IROM_ALIGN == segment.addr % IROM_ALIGN
                checksum = self.save_segment(f, segment, checksum)
            self.append_checksum(f, checksum)
            # kinda hacky: go back to the initial header and write the new segment count
            # that includes padding segments. Luckily(?) this header is not checksummed
            f.seek(1)
            try:
                f.write(chr(len(self.segments) + padding_segments))
            except TypeError:  # Python 3
                f.write(bytes([len(self.segments) + padding_segments]))


class ELFFile(object):
    SEC_TYPE_PROGBITS = 0x01
    SEC_TYPE_STRTAB = 0x03

    LEN_SEC_HEADER = 0x28

    def __init__(self, name):
        # Load sections from the ELF file
        self.name = name
        with open(self.name, 'rb') as f:
            self._read_elf_file(f)

    def get_section(self, section_name):
        for s in self.sections:
            if s.name == section_name:
                return s
        raise ValueError("No section %s in ELF file" % section_name)

    def _read_elf_file(self, f):
        # read the ELF file header
        LEN_FILE_HEADER = 0x34
        try:
            (ident,_type,machine,_version,
             self.entrypoint,_phoff,shoff,_flags,
             _ehsize, _phentsize,_phnum, shentsize,
             shnum,shstrndx) = struct.unpack("<16sHHLLLLLHHHHHH", f.read(LEN_FILE_HEADER))
        except struct.error as e:
            raise FatalError("Failed to read a valid ELF header from %s: %s" % (self.name, e))

        if byte(ident, 0) != 0x7f or ident[1:4] != b'ELF':
            raise FatalError("%s has invalid ELF magic header" % self.name)
        if machine != 0x5e:
            raise FatalError("%s does not appear to be an Xtensa ELF file. e_machine=%04x" % (self.name, machine))
        if shentsize != self.LEN_SEC_HEADER:
            raise FatalError("%s has unexpected section header entry size 0x%x (not 0x28)" % (self.name, shentsize, self.LEN_SEC_HEADER))
        if shnum == 0:
            raise FatalError("%s has 0 section headers" % (self.name))
        self._read_sections(f, shoff, shnum, shstrndx)

    def _read_sections(self, f, section_header_offs, section_header_count, shstrndx):
        f.seek(section_header_offs)
        len_bytes = section_header_count * self.LEN_SEC_HEADER
        section_header = f.read(len_bytes)
        if len(section_header) == 0:
            raise FatalError("No section header found at offset %04x in ELF file." % section_header_offs)
        if len(section_header) != (len_bytes):
            raise FatalError("Only read 0x%x bytes from section header (expected 0x%x.) Truncated ELF file?" % (len(section_header), len_bytes))

        # walk through the section header and extract all sections
        section_header_offsets = range(0, len(section_header), self.LEN_SEC_HEADER)

        def read_section_header(offs):
            name_offs,sec_type,_flags,lma,sec_offs,size = struct.unpack_from("<LLLLLL", section_header[offs:])
            return (name_offs, sec_type, lma, size, sec_offs)
        all_sections = [read_section_header(offs) for offs in section_header_offsets]
        prog_sections = [s for s in all_sections if s[1] == ELFFile.SEC_TYPE_PROGBITS]

        # search for the string table section
        if not (shstrndx * self.LEN_SEC_HEADER) in section_header_offsets:
            raise FatalError("ELF file has no STRTAB section at shstrndx %d" % shstrndx)
        _,sec_type,_,sec_size,sec_offs = read_section_header(shstrndx * self.LEN_SEC_HEADER)
        if sec_type != ELFFile.SEC_TYPE_STRTAB:
            print('WARNING: ELF file has incorrect STRTAB section type 0x%02x' % sec_type)
        f.seek(sec_offs)
        string_table = f.read(sec_size)

        # build the real list of ELFSections by reading the actual section names from the
        # string table section, and actual data for each section from the ELF file itself
        def lookup_string(offs):
            raw = string_table[offs:]
            return raw[:raw.index(b'\x00')]

        def read_data(offs,size):
            f.seek(offs)
            return f.read(size)

        prog_sections = [ELFSection(lookup_string(n_offs), lma, read_data(offs, size)) for (n_offs, _type, lma, size, offs) in prog_sections
                         if lma != 0]
        self.sections = prog_sections


def slip_reader(port):
    """Generator to read SLIP packets from a serial port.
    Yields one full SLIP packet at a time, raises exception on timeout or invalid data.

    Designed to avoid too many calls to serial.read(1), which can bog
    down on slow systems.
    """
    partial_packet = None
    in_escape = False
    while True:
        waiting = port.inWaiting()
        read_bytes = port.read(1 if waiting == 0 else waiting)
        if read_bytes == b'':
            raise FatalError("Timed out waiting for packet %s" % ("header" if partial_packet is None else "content"))
        for b in read_bytes:

            if type(b) is int:
                b = bytes([b])  # python 2/3 compat

            if partial_packet is None:  # waiting for packet header
                if b == b'\xc0':
                    partial_packet = b""
                else:
                    raise FatalError('Invalid head of packet (%r)' % b)
            elif in_escape:  # part-way through escape sequence
                in_escape = False
                if b == b'\xdc':
                    partial_packet += b'\xc0'
                elif b == b'\xdd':
                    partial_packet += b'\xdb'
                else:
                    raise FatalError('Invalid SLIP escape (%r%r)' % (b'\xdb', b))
            elif b == b'\xdb':  # start of escape sequence
                in_escape = True
            elif b == b'\xc0':  # end of packet
                yield partial_packet
                partial_packet = None
            else:  # normal byte in packet
                partial_packet += b


def arg_auto_int(x):
    return int(x, 0)


def div_roundup(a, b):
    """ Return a/b rounded up to nearest integer,
    equivalent result to int(math.ceil(float(int(a)) / float(int(b))), only
    without possible floating point accuracy errors.
    """
    return (int(a) + int(b) - 1) // int(b)


def align_file_position(f, size):
    """ Align the position in the file to the next block of specified size """
    align = (size - 1) - (f.tell() % size)
    f.seek(align, 1)


def flash_size_bytes(size):
    """ Given a flash size of the type passed in args.flash_size
    (ie 512KB or 1MB) then return the size in bytes.
    """
    if "MB" in size:
        return int(size[:size.index("MB")]) * 1024 * 1024
    elif "KB" in size:
        return int(size[:size.index("KB")]) * 1024
    else:
        raise FatalError("Unknown size %s" % size)


def hexify(s):
    if not PYTHON2:
        return ''.join('%02X' % c for c in s)
    else:
        return ''.join('%02X' % ord(c) for c in s)


def unhexify(hs):
    s = bytes()

    for i in range(0, len(hs) - 1, 2):
        hex_string = hs[i:i + 2]

        if not PYTHON2:
            s += bytes([int(hex_string, 16)])
        else:
            s += chr(int(hex_string, 16))

    return s


def pad_to(data, alignment, pad_character=b'\xFF'):
    """ Pad to the next alignment boundary """
    pad_mod = len(data) % alignment
    if pad_mod != 0:
        data += pad_character * (alignment - pad_mod)
    return data


class FatalError(RuntimeError):
    """
    Wrapper class for runtime errors that aren't caused by internal bugs, but by
    ESP8266 responses or input content.
    """
    def __init__(self, message):
        RuntimeError.__init__(self, message)

    @staticmethod
    def WithResult(message, result):
        """
        Return a fatal error object that appends the hex values of
        'result' as a string formatted argument.
        """
        message += " (result was %s)" % hexify(result)
        return FatalError(message)


class NotImplementedInROMError(FatalError):
    """
    Wrapper class for the error thrown when a particular ESP bootloader function
    is not implemented in the ROM bootloader.
    """
    def __init__(self, bootloader, func):
        FatalError.__init__(self, "%s ROM does not support function %s." % (bootloader.CHIP_NAME, func.__name__))

# "Operation" commands, executable at command line. One function each
#
# Each function takes either two args (<ESPLoader instance>, <args>) or a single <args>
# argument.


def load_ram(esp, args):
    image = LoadFirmwareImage(esp, args.filename)

    print('RAM boot...')
    for (offset, size, data) in image.segments:
        print('Downloading %d bytes at %08x...' % (size, offset), end=' ')
        sys.stdout.flush()
        esp.mem_begin(size, div_roundup(size, esp.ESP_RAM_BLOCK), esp.ESP_RAM_BLOCK, offset)

        seq = 0
        while len(data) > 0:
            esp.mem_block(data[0:esp.ESP_RAM_BLOCK], seq)
            data = data[esp.ESP_RAM_BLOCK:]
            seq += 1
        print('done!')

    print('All segments done, executing at %08x' % image.entrypoint)
    esp.mem_finish(image.entrypoint)


def read_mem(esp, args):
    print('0x%08x = 0x%08x' % (args.address, esp.read_reg(args.address)))


def write_mem(esp, args):
    esp.write_reg(args.address, args.value, args.mask, 0)
    print('Wrote %08x, mask %08x to %08x' % (args.value, args.mask, args.address))


def dump_mem(esp, args):
    f = open(args.filename, 'wb')
    for i in range(args.size // 4):
        d = esp.read_reg(args.address + (i * 4))
        f.write(struct.pack(b'<I', d))
        if f.tell() % 1024 == 0:
            print('\r%d bytes read... (%d %%)' % (f.tell(),
                                                  f.tell() * 100 // args.size),
                  end=' ')
        sys.stdout.flush()
    print('Done!')


def detect_flash_size(esp, args):
    if args.flash_size == 'detect':
        flash_id = esp.flash_id()
        size_id = flash_id >> 16
        args.flash_size = DETECTED_FLASH_SIZES.get(size_id)
        if args.flash_size is None:
            print('Warning: Could not auto-detect Flash size (FlashID=0x%x, SizeID=0x%x), defaulting to 4MB' % (flash_id, size_id))
            args.flash_size = '4MB'
        else:
            print('Auto-detected Flash size:', args.flash_size)


def _update_image_flash_params(esp, address, args, image):
    """ Modify the flash mode & size bytes if this looks like an executable bootloader image  """
    if len(image) < 8:
        return image  # not long enough to be a bootloader image

    # unpack the (potential) image header
    magic, _, flash_mode, flash_size_freq = struct.unpack("BBBB", image[:4])
    if address != esp.BOOTLOADER_FLASH_OFFSET or magic != esp.ESP_IMAGE_MAGIC:
        return image  # not flashing a bootloader, so don't modify this

    if args.flash_mode != 'keep':
        flash_mode = {'qio':0, 'qout':1, 'dio':2, 'dout': 3}[args.flash_mode]

    flash_freq = flash_size_freq & 0x0F
    if args.flash_freq != 'keep':
        flash_freq = {'40m':0, '26m':1, '20m':2, '80m': 0xf}[args.flash_freq]

    flash_size = flash_size_freq & 0xF0
    if args.flash_size != 'keep':
        flash_size = esp.parse_flash_size_arg(args.flash_size)

    flash_params = struct.pack(b'BB', flash_mode, flash_size + flash_freq)
    if flash_params != image[2:4]:
        print('Flash params set to 0x%04x' % struct.unpack(">H", flash_params))
        image = image[0:2] + flash_params + image[4:]
    return image


def write_flash(esp, args):
    # set args.compress based on default behaviour:
    # -> if either --compress or --no-compress is set, honour that
    # -> otherwise, set --compress unless --no-stub is set
    if args.compress is None and not args.no_compress:
        args.compress = not args.no_stub

    # verify file sizes fit in flash
    flash_end = flash_size_bytes(args.flash_size)
    for address, argfile in args.addr_filename:
        argfile.seek(0,2)  # seek to end
        if address + argfile.tell() > flash_end:
            raise FatalError(("File %s (length %d) at offset %d will not fit in %d bytes of flash. " +
                             "Use --flash-size argument, or change flashing address.")
                             % (argfile.name, argfile.tell(), address, flash_end))
        argfile.seek(0)

    for address, argfile in args.addr_filename:
        if args.no_stub:
            print('Erasing flash...')
        image = pad_to(argfile.read(), 4)
        image = _update_image_flash_params(esp, address, args, image)
        calcmd5 = hashlib.md5(image).hexdigest()
        uncsize = len(image)
        if args.compress:
            uncimage = image
            image = zlib.compress(uncimage, 9)
            ratio = uncsize / len(image)
            blocks = esp.flash_defl_begin(uncsize, len(image), address)
        else:
            ratio = 1.0
            blocks = esp.flash_begin(uncsize, address)
        argfile.seek(0)  # in case we need it again
        seq = 0
        written = 0
        t = time.time()
        esp._port.timeout = min(DEFAULT_TIMEOUT * ratio,
                                CHIP_ERASE_TIMEOUT * 2)
        while len(image) > 0:
            print('\rWriting at 0x%08x... (%d %%)' % (address + seq * esp.FLASH_WRITE_SIZE, 100 * (seq + 1) // blocks), end='')
            sys.stdout.flush()
            block = image[0:esp.FLASH_WRITE_SIZE]
            if args.compress:
                esp.flash_defl_block(block, seq)
            else:
                # Pad the last block
                block = block + b'\xff' * (esp.FLASH_WRITE_SIZE - len(block))
                esp.flash_block(block, seq)
            image = image[esp.FLASH_WRITE_SIZE:]
            seq += 1
            written += len(block)
        t = time.time() - t
        speed_msg = ""
        if args.compress:
            if t > 0.0:
                speed_msg = " (effective %.1f kbit/s)" % (uncsize / t * 8 / 1000)
            print('\rWrote %d bytes (%d compressed) at 0x%08x in %.1f seconds%s...' % (uncsize, written, address, t, speed_msg))
        else:
            if t > 0.0:
                speed_msg = " (%.1f kbit/s)" % (written / t * 8 / 1000)
            print('\rWrote %d bytes at 0x%08x in %.1f seconds%s...' % (written, address, t, speed_msg))
        try:
            res = esp.flash_md5sum(address, uncsize)
            if res != calcmd5:
                print('File  md5: %s' % calcmd5)
                print('Flash md5: %s' % res)
                print('MD5 of 0xFF is %s' % (hashlib.md5(b'\xFF' * uncsize).hexdigest()))
                raise FatalError("MD5 of file does not match data in flash!")
            else:
                print('Hash of data verified.')
        except NotImplementedInROMError:
            pass
        esp._port.timeout = DEFAULT_TIMEOUT

    print('\nLeaving...')

    if esp.IS_STUB:
        # skip sending flash_finish to ROM loader here,
        # as it causes the loader to exit and run user code
        esp.flash_begin(0, 0)
        if args.compress:
            esp.flash_defl_finish(False)
        else:
            esp.flash_finish(False)

    if args.verify:
        print('Verifying just-written flash...')
        print('(This option is deprecated, flash contents are now always read back after flashing.)')
        verify_flash(esp, args)


def image_info(args):
    image = LoadFirmwareImage(args.chip, args.filename)
    print('Image version: %d' % image.version)
    print('Entry point: %08x' % image.entrypoint if image.entrypoint != 0 else 'Entry point not set')
    print('%d segments' % len(image.segments))
    print
    idx = 0
    for seg in image.segments:
        idx += 1
        print('Segment %d: %r' % (idx, seg))
    calc_checksum = image.calculate_checksum()
    print('Checksum: %02x (%s)' % (image.checksum,
                                   'valid' if image.checksum == calc_checksum else 'invalid - calculated %02x' % calc_checksum))


def make_image(args):
    image = ESPFirmwareImage()
    if len(args.segfile) == 0:
        raise FatalError('No segments specified')
    if len(args.segfile) != len(args.segaddr):
        raise FatalError('Number of specified files does not match number of specified addresses')
    for (seg, addr) in zip(args.segfile, args.segaddr):
        data = open(seg, 'rb').read()
        image.segments.append(ImageSegment(addr, data))
    image.entrypoint = args.entrypoint
    image.save(args.output)


def elf2image(args):
    e = ELFFile(args.input)
    if args.chip == 'auto':  # Default to ESP8266 for backwards compatibility
        print("Creating image for ESP8266...")
        args.chip == 'esp8266'

    if args.chip == 'esp32':
        image = ESP32FirmwareImage()
    elif args.version == '1':  # ESP8266
        image = ESPFirmwareImage()
    else:
        image = OTAFirmwareImage()
    image.entrypoint = e.entrypoint
    image.segments = e.sections  # ELFSection is a subclass of ImageSegment
    image.flash_mode = {'qio':0, 'qout':1, 'dio':2, 'dout': 3}[args.flash_mode]
    image.flash_size_freq = image.ROM_LOADER.FLASH_SIZES[args.flash_size]
    image.flash_size_freq += {'40m':0, '26m':1, '20m':2, '80m': 0xf}[args.flash_freq]

    if args.output is None:
        args.output = image.default_output_name(args.input)
    image.save(args.output)


def read_mac(esp, args):
    mac = esp.read_mac()

    def print_mac(label, mac):
        print('%s: %s' % (label, ':'.join(map(lambda x: '%02x' % x, mac))))
    print_mac("MAC", mac)


def chip_id(esp, args):
    chipid = esp.chip_id()
    print('Chip ID: 0x%08x' % chipid)


def erase_flash(esp, args):
    print('Erasing flash (this may take a while)...')
    t = time.time()
    esp.erase_flash()
    print('Chip erase completed successfully in %.1fs' % (time.time() - t))


def erase_region(esp, args):
    print('Erasing region (may be slow depending on size)...')
    t = time.time()
    esp.erase_region(args.address, args.size)
    print('Erase completed successfully in %.1f seconds.' % (time.time() - t))


def run(esp, args):
    esp.run()


def flash_id(esp, args):
    flash_id = esp.flash_id()
    print('Manufacturer: %02x' % (flash_id & 0xff))
    flid_lowbyte = (flash_id >> 16) & 0xFF
    print('Device: %02x%02x' % ((flash_id >> 8) & 0xff, flid_lowbyte))
    print('Detected flash size: %s' % (DETECTED_FLASH_SIZES.get(flid_lowbyte, "Unknown")))


def read_flash(esp, args):
    if args.no_progress:
        flash_progress = None
    else:
        def flash_progress(progress, length):
            msg = '%d (%d %%)' % (progress, progress * 100.0 / length)
            padding = '\b' * len(msg)
            if progress == length:
                padding = '\n'
            sys.stdout.write(msg + padding)
            sys.stdout.flush()
    t = time.time()
    data = esp.read_flash(args.address, args.size, flash_progress)
    t = time.time() - t
    print('\rRead %d bytes at 0x%x in %.1f seconds (%.1f kbit/s)...'
          % (len(data), args.address, t, len(data) / t * 8 / 1000))
    open(args.filename, 'wb').write(data)


def verify_flash(esp, args):
    differences = False

    for address, argfile in args.addr_filename:
        image = pad_to(argfile.read(), 4)
        argfile.seek(0)  # rewind in case we need it again

        image = _update_image_flash_params(esp, address, args, image)

        image_size = len(image)
        print('Verifying 0x%x (%d) bytes @ 0x%08x in flash against %s...' % (image_size, image_size, address, argfile.name))
        # Try digest first, only read if there are differences.
        digest = esp.flash_md5sum(address, image_size)
        expected_digest = hashlib.md5(image).hexdigest()
        if digest == expected_digest:
            print('-- verify OK (digest matched)')
            continue
        else:
            differences = True
            if getattr(args, 'diff', 'no') != 'yes':
                print('-- verify FAILED (digest mismatch)')
                continue

        flash = esp.read_flash(address, image_size)
        assert flash != image
        diff = [i for i in range(image_size) if flash[i] != image[i]]
        print('-- verify FAILED: %d differences, first @ 0x%08x' % (len(diff), address + diff[0]))
        for d in diff:
            flash_byte = flash[d]
            image_byte = image[d]
            if PYTHON2:
                flash_byte = ord(flash_byte)
                image_byte = ord(image_byte)
            print('   %08x %02x %02x' % (address + d, flash_byte, image_byte))
    if differences:
        raise FatalError("Verify failed.")


def read_flash_status(esp, args):
    print('Status value: 0x%04x' % esp.read_status(args.bytes))


def write_flash_status(esp, args):
    fmt = "0x%%0%dx" % (args.bytes * 2)
    args.value = args.value & ((1 << (args.bytes * 8)) - 1)
    print(('Initial flash status: ' + fmt) % esp.read_status(args.bytes))
    print(('Setting flash status: ' + fmt) % args.value)
    esp.write_status(args.value, args.bytes, args.non_volatile)
    print(('After flash status:   ' + fmt) % esp.read_status(args.bytes))


def version(args):
    print(__version__)

#
# End of operations functions
#


def main():
    parser = argparse.ArgumentParser(description='esptool.py v%s - ESP8266 ROM Bootloader Utility' % __version__, prog='esptool')

    parser.add_argument('--chip', '-c',
                        help='Target chip type',
                        choices=['auto', 'esp8266', 'esp32'],
                        default=os.environ.get('ESPTOOL_CHIP', 'auto'))

    parser.add_argument(
        '--port', '-p',
        help='Serial port device',
        default=os.environ.get('ESPTOOL_PORT', ESPLoader.DEFAULT_PORT))

    parser.add_argument(
        '--baud', '-b',
        help='Serial port baud rate used when flashing/reading',
        type=arg_auto_int,
        default=os.environ.get('ESPTOOL_BAUD', ESPLoader.ESP_ROM_BAUD))

    parser.add_argument(
        '--before',
        help='What to do before connecting to the chip',
        choices=['default_reset', 'no_reset'],
        default=os.environ.get('ESPTOOL_BEFORE', 'default_reset'))

    parser.add_argument(
        '--after', '-a',
        help='What to do after esptool.py is finished',
        choices=['hard_reset', 'soft_reset', 'no_reset'],
        default=os.environ.get('ESPTOOL_AFTER', 'hard_reset'))

    parser.add_argument(
        '--no-stub',
        help="Disable launching the flasher stub, only talk to ROM bootloader. Some features will not be available.",
        action='store_true')

    subparsers = parser.add_subparsers(
        dest='operation',
        help='Run esptool {command} -h for additional help')

    def add_spi_connection_arg(parent):
        parent.add_argument('--spi-connection', '-sc', help='ESP32-only argument. Override default SPI Flash connection. ' +
                            'Value can be SPI, HSPI or a comma-separated list of 5 I/O numbers to use for SPI flash (CLK,Q,D,HD,CS).',
                            action=SpiConnectionAction)

    parser_load_ram = subparsers.add_parser(
        'load_ram',
        help='Download an image to RAM and execute')
    parser_load_ram.add_argument('filename', help='Firmware image')

    parser_dump_mem = subparsers.add_parser(
        'dump_mem',
        help='Dump arbitrary memory to disk')
    parser_dump_mem.add_argument('address', help='Base address', type=arg_auto_int)
    parser_dump_mem.add_argument('size', help='Size of region to dump', type=arg_auto_int)
    parser_dump_mem.add_argument('filename', help='Name of binary dump')

    parser_read_mem = subparsers.add_parser(
        'read_mem',
        help='Read arbitrary memory location')
    parser_read_mem.add_argument('address', help='Address to read', type=arg_auto_int)

    parser_write_mem = subparsers.add_parser(
        'write_mem',
        help='Read-modify-write to arbitrary memory location')
    parser_write_mem.add_argument('address', help='Address to write', type=arg_auto_int)
    parser_write_mem.add_argument('value', help='Value', type=arg_auto_int)
    parser_write_mem.add_argument('mask', help='Mask of bits to write', type=arg_auto_int)

    def add_spi_flash_subparsers(parent, is_elf2image):
        """ Add common parser arguments for SPI flash properties """
        extra_keep_args = [] if is_elf2image else ['keep']
        auto_detect = not is_elf2image

        parent.add_argument('--flash_freq', '-ff', help='SPI Flash frequency',
                            choices=extra_keep_args + ['40m', '26m', '20m', '80m'],
                            default=os.environ.get('ESPTOOL_FF', '40m' if is_elf2image else 'keep'))
        parent.add_argument('--flash_mode', '-fm', help='SPI Flash mode',
                            choices=extra_keep_args + ['qio', 'qout', 'dio', 'dout'],
                            default=os.environ.get('ESPTOOL_FM', 'qio' if is_elf2image else 'keep'))
        parent.add_argument('--flash_size', '-fs', help='SPI Flash size in MegaBytes (1MB, 2MB, 4MB, 8MB, 16M)'
                            ' plus ESP8266-only (256KB, 512KB, 2MB-c1, 4MB-c1)',
                            action=FlashSizeAction, auto_detect=auto_detect,
                            default=os.environ.get('ESPTOOL_FS', 'detect' if auto_detect else '1MB'))
        add_spi_connection_arg(parent)

    parser_write_flash = subparsers.add_parser(
        'write_flash',
        help='Write a binary blob to flash')
    parser_write_flash.add_argument('addr_filename', metavar='<address> <filename>', help='Address followed by binary filename, separated by space',
                                    action=AddrFilenamePairAction)
    add_spi_flash_subparsers(parser_write_flash, is_elf2image=False)
    parser_write_flash.add_argument('--no-progress', '-p', help='Suppress progress output', action="store_true")
    parser_write_flash.add_argument('--verify', help='Verify just-written data on flash ' +
                                    '(mostly superfluous, data is read back during flashing)', action='store_true')
    compress_args = parser_write_flash.add_mutually_exclusive_group(required=False)
    compress_args.add_argument('--compress', '-z', help='Compress data in transfer (default unless --no-stub is specified)',action="store_true", default=None)
    compress_args.add_argument('--no-compress', '-u', help='Disable data compression during transfer (default if --no-stub is specified)',action="store_true")

    subparsers.add_parser(
        'run',
        help='Run application code in flash')

    parser_image_info = subparsers.add_parser(
        'image_info',
        help='Dump headers from an application image')
    parser_image_info.add_argument('filename', help='Image file to parse')

    parser_make_image = subparsers.add_parser(
        'make_image',
        help='Create an application image from binary files')
    parser_make_image.add_argument('output', help='Output image file')
    parser_make_image.add_argument('--segfile', '-f', action='append', help='Segment input file')
    parser_make_image.add_argument('--segaddr', '-a', action='append', help='Segment base address', type=arg_auto_int)
    parser_make_image.add_argument('--entrypoint', '-e', help='Address of entry point', type=arg_auto_int, default=0)

    parser_elf2image = subparsers.add_parser(
        'elf2image',
        help='Create an application image from ELF file')
    parser_elf2image.add_argument('input', help='Input ELF file')
    parser_elf2image.add_argument('--output', '-o', help='Output filename prefix (for version 1 image), or filename (for version 2 single image)', type=str)
    parser_elf2image.add_argument('--version', '-e', help='Output image version', choices=['1','2'], default='1')

    add_spi_flash_subparsers(parser_elf2image, is_elf2image=True)

    subparsers.add_parser(
        'read_mac',
        help='Read MAC address from OTP ROM')

    subparsers.add_parser(
        'chip_id',
        help='Read Chip ID from OTP ROM')

    parser_flash_id = subparsers.add_parser(
        'flash_id',
        help='Read SPI flash manufacturer and device ID')
    add_spi_connection_arg(parser_flash_id)

    parser_read_status = subparsers.add_parser(
        'read_flash_status',
        help='Read SPI flash status register')

    add_spi_connection_arg(parser_read_status)
    parser_read_status.add_argument('--bytes', help='Number of bytes to read (1-3)', type=int, choices=[1,2,3], default=2)

    parser_write_status = subparsers.add_parser(
        'write_flash_status',
        help='Write SPI flash status register')

    add_spi_connection_arg(parser_write_status)
    parser_write_status.add_argument('--non-volatile', help='Write non-volatile bits (use with caution)', action='store_true')
    parser_write_status.add_argument('--bytes', help='Number of status bytes to write (1-3)', type=int, choices=[1,2,3], default=2)
    parser_write_status.add_argument('value', help='New value', type=arg_auto_int)

    parser_read_flash = subparsers.add_parser(
        'read_flash',
        help='Read SPI flash content')
    add_spi_connection_arg(parser_read_flash)
    parser_read_flash.add_argument('address', help='Start address', type=arg_auto_int)
    parser_read_flash.add_argument('size', help='Size of region to dump', type=arg_auto_int)
    parser_read_flash.add_argument('filename', help='Name of binary dump')
    parser_read_flash.add_argument('--no-progress', '-p', help='Suppress progress output', action="store_true")

    parser_verify_flash = subparsers.add_parser(
        'verify_flash',
        help='Verify a binary blob against flash')
    parser_verify_flash.add_argument('addr_filename', help='Address and binary file to verify there, separated by space',
                                     action=AddrFilenamePairAction)
    parser_verify_flash.add_argument('--diff', '-d', help='Show differences',
                                     choices=['no', 'yes'], default='no')
    add_spi_flash_subparsers(parser_verify_flash, is_elf2image=False)

    parser_erase_flash = subparsers.add_parser(
        'erase_flash',
        help='Perform Chip Erase on SPI flash')
    add_spi_connection_arg(parser_erase_flash)

    parser_erase_region = subparsers.add_parser(
        'erase_region',
        help='Erase a region of the flash')
    add_spi_connection_arg(parser_erase_region)
    parser_erase_region.add_argument('address', help='Start address (must be multiple of 4096)', type=arg_auto_int)
    parser_erase_region.add_argument('size', help='Size of region to erase (must be multiple of 4096)', type=arg_auto_int)

    subparsers.add_parser(
        'version', help='Print esptool version')

    # internal sanity check - every operation matches a module function of the same name
    for operation in subparsers.choices.keys():
        assert operation in globals(), "%s should be a module function" % operation

    expand_file_arguments()

    args = parser.parse_args()

    print('esptool.py v%s' % __version__)

    # operation function can take 1 arg (args), 2 args (esp, arg)
    # or be a member function of the ESPLoader class.

    if args.operation is None:
        parser.print_help()
        sys.exit(1)

    operation_func = globals()[args.operation]
    operation_args,_,_,_ = inspect.getargspec(operation_func)
    if operation_args[0] == 'esp':  # operation function takes an ESPLoader connection object
        initial_baud = min(ESPLoader.ESP_ROM_BAUD, args.baud)  # don't sync faster than the default baud rate
        if args.chip == 'auto':
            esp = ESPLoader.detect_chip(args.port, initial_baud, args.before)
        else:
            chip_class = {
                'esp8266': ESP8266ROM,
                'esp32': ESP32ROM,
            }[args.chip]
            esp = chip_class(args.port, initial_baud)
            esp.connect(args.before)

        print("Chip is %s" % (esp.get_chip_description()))

        if not args.no_stub:
            esp = esp.run_stub()

        if args.baud > initial_baud:
            try:
                esp.change_baud(args.baud)
            except NotImplementedInROMError:
                print("WARNING: ROM doesn't support changing baud rate. Keeping initial baud rate %d" % initial_baud)

        # override common SPI flash parameter stuff if configured to do so
        if hasattr(args, "spi_connection") and args.spi_connection is not None:
            if esp.CHIP_NAME != "ESP32":
                raise FatalError("Chip %s does not support --spi-connection option." % esp.CHIP_NAME)
            print("Configuring SPI flash mode...")
            esp.flash_spi_attach(args.spi_connection)
        elif args.no_stub:
            print("Enabling default SPI flash mode...")
            # ROM loader doesn't enable flash unless we explicitly do it
            esp.flash_spi_attach(0)

        if hasattr(args, "flash_size"):
            print("Configuring flash size...")
            detect_flash_size(esp, args)
            esp.flash_set_parameters(flash_size_bytes(args.flash_size))

        operation_func(esp, args)

        # finish execution based on args.after
        if args.after == 'hard_reset':
            print('Hard resetting...')
            esp.hard_reset()
        elif args.after == 'soft_reset':
            print('Soft resetting...')
            # flash_finish will trigger a soft reset
            esp.soft_reset(False)
        else:
            print('Staying in bootloader.')
            if esp.IS_STUB:
                esp.soft_reset(True)  # exit stub back to ROM loader

    else:
        operation_func(args)


def expand_file_arguments():
    """ Any argument starting with "@" gets replaced with all values read from a text file.
    Text file arguments can be split by newline or by space.
    Values are added "as-is", as if they were specified in this order on the command line.
    """
    new_args = []
    expanded = False
    for arg in sys.argv:
        if arg.startswith("@"):
            expanded = True
            with open(arg[1:],"r") as f:
                for line in f.readlines():
                    new_args += shlex.split(line)
        else:
            new_args.append(arg)
    if expanded:
        print("esptool.py %s" % (" ".join(new_args[1:])))
        sys.argv = new_args


class FlashSizeAction(argparse.Action):
    """ Custom flash size parser class to support backwards compatibility with megabit size arguments.

    (At next major relase, remove deprecated sizes and this can become a 'normal' choices= argument again.)
    """
    def __init__(self, option_strings, dest, nargs=1, auto_detect=False, **kwargs):
        super(FlashSizeAction, self).__init__(option_strings, dest, nargs, **kwargs)
        self._auto_detect = auto_detect

    def __call__(self, parser, namespace, values, option_string=None):
        try:
            value = {
                '2m': '256KB',
                '4m': '512KB',
                '8m': '1MB',
                '16m': '2MB',
                '32m': '4MB',
                '16m-c1': '2MB-c1',
                '32m-c1': '4MB-c1',
            }[values[0]]
            print("WARNING: Flash size arguments in megabits like '%s' are deprecated." % (values[0]))
            print("Please use the equivalent size '%s'." % (value))
            print("Megabit arguments may be removed in a future release.")
        except KeyError:
            value = values[0]

        known_sizes = dict(ESP8266ROM.FLASH_SIZES)
        known_sizes.update(ESP32ROM.FLASH_SIZES)
        if self._auto_detect:
            known_sizes['detect'] = 'detect'
        if value not in known_sizes:
            raise argparse.ArgumentError(self, '%s is not a known flash size. Known sizes: %s' % (value, ", ".join(known_sizes.keys())))
        setattr(namespace, self.dest, value)


class SpiConnectionAction(argparse.Action):
    """ Custom action to parse 'spi connection' override. Values are SPI, HSPI, or a sequence of 5 pin numbers separated by commas.
    """
    def __call__(self, parser, namespace, value, option_string=None):
        if value.upper() == "SPI":
            value = 0
        elif value.upper() == "HSPI":
            value = 1
        elif "," in value:
            values = value.split(",")
            if len(values) != 5:
                raise argparse.ArgumentError(self, '%s is not a valid list of comma-separate pin numbers. Must be 5 numbers - CLK,Q,D,HD,CS.' % value)
            try:
                values = tuple(int(v,0) for v in values)
            except ValueError:
                raise argparse.ArgumentError(self, '%s is not a valid argument. All pins must be numeric values' % values)
            if any([v for v in values if v > 33 or v < 0]):
                raise argparse.ArgumentError(self, 'Pin numbers must be in the range 0-33.')
            # encode the pin numbers as a 32-bit integer with packed 6-bit values, the same way ESP32 ROM takes them
            # TODO: make this less ESP32 ROM specific somehow...
            clk,q,d,hd,cs = values
            value = (hd << 24) | (cs << 18) | (d << 12) | (q << 6) | clk
        else:
            raise argparse.ArgumentError(self, '%s is not a valid spi-connection value. ' +
                                         'Values are SPI, HSPI, or a sequence of 5 pin numbers CLK,Q,D,HD,CS).' % values)
        setattr(namespace, self.dest, value)


class AddrFilenamePairAction(argparse.Action):
    """ Custom parser class for the address/filename pairs passed as arguments """
    def __init__(self, option_strings, dest, nargs='+', **kwargs):
        super(AddrFilenamePairAction, self).__init__(option_strings, dest, nargs, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        # validate pair arguments
        pairs = []
        for i in range(0,len(values),2):
            try:
                address = int(values[i],0)
            except ValueError as e:
                raise argparse.ArgumentError(self,'Address "%s" must be a number' % values[i])
            try:
                argfile = open(values[i + 1], 'rb')
            except IOError as e:
                raise argparse.ArgumentError(self, e)
            except IndexError:
                raise argparse.ArgumentError(self,'Must be pairs of an address and the binary filename to write there')
            pairs.append((address, argfile))

        # Sort the addresses and check for overlapping
        end = 0
        for address, argfile in sorted(pairs):
            argfile.seek(0,2)  # seek to end
            size = argfile.tell()
            argfile.seek(0)
            sector_start = address & ~(ESPLoader.FLASH_SECTOR_SIZE - 1)
            sector_end = ((address + size + ESPLoader.FLASH_SECTOR_SIZE - 1) & ~(ESPLoader.FLASH_SECTOR_SIZE - 1)) - 1
            if sector_start < end:
                message = 'Detected overlap at address: 0x%x for file: %s' % (address, argfile.name)
                raise argparse.ArgumentError(self, message)
            end = sector_end
        setattr(namespace, self.dest, pairs)


# Binary stub code (see flasher_stub dir for source & details)
ESP8266ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
""")))
ESP8266ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
eNrNXXlj1Eay/yrS2BjbmKRbmtFhIJkZzAQI7IKJHUgmWUstCcID1h5m14Ql3/11XeqWZowhx773h8no6qOquupXR3f+c3VZv1te3Q/Kq/N3RTZ/p9X8nVJj+4+ev2sa+JtN4Fb3L7N/Tf313+9O7tnvhjG897V9\
ZOxViY+4uRyaHNMT+vik15pe/1t779A4Vkfh3+cRzd/ltqcyljEo78I2edVv4F80PhX7U/B/ed+Wbo7cGbUR7HjDsRPOKvzgqTegIpNP8yxpf9k/IVQ2lNvwjS5di3b4i960s7bn+VJ+PrL/1N6FjrwmjPReKvml\
m3bUN+0bOY9DtcPLzMgbkfJGpNwTM2wbtk2OPDroHrt8juCYSv9Cui9BRBoWvyzzLgp38RS/Gu89wP+oG/ifd3dFaNV9/lUO7/EvY77gX9p2UEd8UWU5/nrR3rONVNJjbgdWozSOH2zJkLjJ0LbJwpfbLwtNwgqf\
aA3PBsXGgEQPZx8Vt+3dqJja9qNiAv0VtrkmKr4mka9Tas20fLZdlMgL+7Tkp7iCLMmBSW6hTJE3A+gAHqf23ybh3jMThMxBY4eQWRYV0JCG5rU0z8yC76uIBMxY4YJWXwWuW2UOqd+qWDPawsBNpobSbRPAmEgN\
g/YGED3ag3+4tWG/tYvu25sFyt5Efjy2P5BKZ/KDhxuVPBBuzDRrGjOJ3KTJbmxY/iVRl9j8EMgDz+E2LC6+PTUbgwkIxoC/0NPHt/HOaFoMWD50Jk/jSMYHXBmAuKhB0Ezny+29ts1teD4oBsxDw1MoTX8KwmQ7\
Sl1wF1l8x95l0jbSXTzw+6V2tA7gRzAgPQcC3FhBK2HA9r9qRIpUae6mrnkc0QXjaAeqVhkKpK5qlhAiFP3XCpzVyHlMY4PXMtQjafS4kQHbmzkrtyZ5u9Hgy7Of5M7t+ZtmQ159wH3CN5WvOJvb+NUZ/n7idRe7\
EeZZV2XlncGp5D2NDJZI89ZrQkxiwi+DpqKvZu88Bei1NnsN92f2G9aS2vQIkVNf2w1pTprdWF6GG3Ygb6jlpjfOLxwRstR9ov0BTOX+wLv5TEYVeXytNLyh4z3b4VLuKboHwg2j/a0nC122ZskV/1ncfca/Rz6t\
dAVqG+wUknhO8qiS1uA1TDqSA3x25uuP96syWFu1VVck1Rp7ft1a0j1AOPq8/9ExL+CCNGMFph1n/wW9lZmHAcjg8PgJmDBWjRFYjgmrkYSVp8MLsOxgwPqfK90dEj1rRX0Z7OtL/pF+RXOAPtBgrTZN03h+0TSS\
tdOwT4uKhm+S7x0PAFDA67S2t1qCPxVpN0x5YUjZCEsL4cmNlUdf0yOT/M3n9pa8MnsIt7MHrJXWjiUS2fOW/OwGdwnNDblHHX1WQzPRBPvUFtBJDbvgNySZbC0EMoLBVttuQhbdLWaELNkeYI5DEhA0SCA6AMmM\
U6HcTA6WAhdAJuq3mbme6uL21DEf8GJdjweowb+A9g95dKNSDNmUf6C6OgLtL4o4PTlCs3MANx8dBPACDFyP4wBhhZJpaZlzgIvYDnJ2zaOLYnPqyODRRifxfJlF3tPsmDVbFrEuQuKYJHAaKyM10ggdA8dkhLso\
O7OglcG/owhdEemjldsRQJVsiQD2PA/+WrTVaN0iIHWl085nrehueP1iyxPmce3z/B3jCpN2JaYx/9RkZRu/z/wF+SdNmuzB5wHId3dMeSsroJHoGjEijnPXXuQMp7NvB3SlRrvfB/QWIlkwanXzjPElukQzdDxG\
raLluY+8dVY5Gq2Sk5SUYGAZLwqICkCPjxYMfvHSjM48sCFYQnzQji5rQDWWLeKSXgC96MhKTIwqYCoMR2tlJ9aU3h2YwnALBXS2jT6u46s2GylR0T60XYEMDSMxbNjLLbaoccq+FrY74MGuyAg4DBkxFmcUs7pt\
X8j24BXA+bWaTHY3+T3Vf+8WdHV9LpSr+8+BfLbxOuMXiv4LLJ4j3z8bIBpHTB5P4d/h0/n8zr+giRkDQ3x3PZqMEUrGAQghzAt1BkujGv3AfEwAq3Q9+I+DYnZokAROFxbXWPRqRg5oA8X9qB8Tt2DKZTRgydPi\
bpYsKPEAFni0CK+VxRXCq2xtr6bi6vBqivCFCLwNM/pWAHA4KojOZPJ/PPmWTXRxAL7yEoQnvHZY7CyKvfH37BwW5HvBAsVFlPwT+rK2uixFvb3h9QcQANfxHnx7CP+Otl/hcLbgdrF5WOzefAIa8wMsM3hh+AJU\
CKjLMnZyjqGEoSZbZGULl9c2PUdaRCyemYgnGwmkQPwL9PYLdJyD6OfkWhTp1zlBKZWUxWZZbJ3Yp0mwCIGuZgP0joZG04YaBcSFxhCN873yJ4oomIqc+ixx7laRkjqtYcGRxx/+Sq3AXEwDqgxWJQ5S5YRVOy0N\
RVabrtn3vkcPfPM13a+RqmjsaxjAzWszz3GRliOa3JVHGCILX7mZqfhZOyOB3u00EjeNF71p5ILh4n5cSxaECivvG4PfhCXfAoGPIcoUvWCVr67A2nk5mBbqsBiWxZfALhBTEmCQ3cysUQjI6mmoDsNhGeJHYUxi\
TuuuJnc9aEiSjfn3o2Ao6zML0Il69B04veWReMhnT1meMDKEfgu65M9TjzGj8dhKTk64YnnC04jVLwFQdsZtJSvsCGfQ+N7tnOg+o2BBl47MkSa5NUam7rCN8h9Sayy2gwDRoCKmYjDFxOEN6CkvRXapEbQIscfl\
SNg6kNlxD6o1iwMXASVu8u9qLHob/PEasFVWsjgCjmwDnGeaKGrN5eYOBIWCcLJDRgP8hTqekJWFSTXVMTBhA23tJiqF6gaSYfNCMjgZHwTbHH01T47JvjWFv7i8mWfrZz7z0cDvmHrWmTpPg4NpY54wcEp/gGEH\
9JFWTn/p5CEBlQbEs8px8hsfmXzeTn5HWjLHZHua4ezTZ/4HeY4BWLS4IQG4puboYlO/HOwPQNimZJxaZrPHWGcTmXtXodiZTz5V+jVaEYRYuZEI0mLH0PdlTSxxWjqk/ptqQsakqVuF93JwfyA0ojFzxw6bTqin\
pnoZ348Ht+GdltQhSwC0DOqyqVq1CC0LFYSwGsbTJDMP43GgKtOAl9D8qywHnoCxyxTFwDAAprIbGNXZ9xGIJrI2lRpgtAOxRsIw2KwQcu8ti60Xeifhu4ksuPLpwnczPiZLWyf80bDPUTEvf5niaZRbfbU6XS7A\
SLZi5mTP80qVunl7RlFEFa3qlh2KRpUjatzOGVyxEqd/RwZ45EKsBA4dNKgUOsYnmxi0u0qhO2gRGVL1QnfWf0EQ1RvJItw5d2NQrSR62m8PURSmWaLZewfp13BujwcBSyNbw1fkk6GsQo4UMOo9/PMIf55TNFVp\
CJ9F5xTyp6vkOqgvgPsGFFlKBn2B8Ktn06ucXaJWQBZhJLacrDhYdOjXvD86bTjmA7LZZBytgPFGdrEvZn03rjcjzO/FRDny7bacB5QloZOpwXNYR3uCz2ExVtPn5KLRp6OPTApTS/1JSSgk2z0HSMvzdlO0M7bz\
BsqlU+4jm94W0YrPGQaDs2uiU0rViYTlw6mERMsBu39NOpA0gqR5gMtm2fd3p3fbT2mVZZk0MYIvwWyjcsk4Sp9Ke83u3cWB+5jhO8YH0R3QHoYF6mZIl5eQHOBl5xn3K5+OcSgjx2rGmP8zNYMubBMuiJUERb3Z\
TU75ATQVYVOAu/R4xvwFatXog6rABU3XAIW7KIg/QnP342ALPockEQRq0HSUSYI6oHEjsd4wDvsQAogrSDrpC6hwyYqgj6FnLDV+1jq5dblNWIPGAOUdk4Ux0f8DyxD+De3zrb5IWpKrzd3NybdEIodKndluIasl\
foikhNWt45Sdem1iZA+qGnBY9dltnzOnC6AQrvLx6Tsw2wvAwk/BLdEH4v5Yh1n7rFsUqNr1j6u8s+p5fnWCKoVmvrvjha+UPu5/AkqnqRYhtohj2p1fnVK0GTNC+vFqL5ap2kU7IN9kMpQX+ALibpjQi7ZJMK2n\
fx0n8cWqX5b4wXenI+dXdzFBFfsKCdeMmm6IuB9MDf20w/mCbCjoqpoiH0tSrZpVrNLX58uHWGpgiCHAuwzDPguktr2y7kGe4oSWdJXB15CUbAhPoQLeId7nxQFnteqRi7U0yaZLC4L1zVn3OcVAUZTcixflaoOU\
esZxUK0+EGrVyQ5n4y8w3XFIbk1jcsakGPeMfFpChymnw4SiKI3oCmdA1bseSEmnRdLS17ZQZKdpwDF+raMijcJkGqbY/nARJlGxPY6DaZidnuFKOFgUybTIviHJqDgsgiNIU3V6l5miDlzAfjzW02Lbuac4xIzz\
hGAsCojh0eCndkbjt9DANNwGNsXT7+FqwcEsTP+CO8n00I18pU7BQI7P8VtmNUYCqgG28BBT1hwRqFU+EYIw+bFEIbIzP4WZnx7AogA+peNvkM5wB1u2fvzSzgf6GEq0AZaUHfDgO1Ty0zYyWC9CpPa5pZr9qfTE\
Uhh0gWntW0pjLctFmEJ/2SmSnvL6KlO8XHMcxBjF6DSmueXRE6ca89xfKzp38fCykjqQ8PrWjrtfpC4nnFXOPIDurjjNTu9K/hkC9TDyIhnIox2JHcfkldWoqIZnnLAzuxunAxjtwAPMtNwCWEi5pFZ1wDEW+1pK\
Y1aeGmplB1mmlvjVVUbG6ExdcZNpS4EMYQeazA4tVyxZMR8IWHpGGOppNNWVjEE2h/dxLcdE7MhFB0Hm61hil9NrFhEBBkZMx5UvTSI+KAQzVAeHXWZC0W2L2a3P/4tuvWN95DmoqedcpCvBv6mrlMjK650+Ylfd\
wqhoE3vdCKjjazQqMbwYjEU06gnRf3wJinwJQm2lApEg1Igq19A2aBSK5bd2U5PCx2oNXKvMfl0KNBk6GQBGtDIwQBPRirDo9SqB9CXqlJhTY1IApQYUAEfPUcITGNLvYD0vfZ4DwbUOAWYaDTkIQ2GUHJGIBA4M\
ZaoX0jA6KZiPUc4ggW1UZA2y+GSnXSYZLR8UrvT1HFzly9woSh7NfkTw+5qol+G0Miz8odRHi6gGBQfxvr40iLcSx9Jm45hEIYtXMWMr9+klgTxP6A27DEovws1V2XdypzISx/Nb0En4jOZJ7LOz3WRapwwVPNt1\
Dg2t0gFGdA5cPoe57Z6HgAnNJENR3ro/kArJjjQQOCCB4Ca1EcwGQCSfL/W3KBkH+wcR0Udf4nb/THNx2M4iNHK73zc99N/1Ds424csp+mEaHT4d7RJ3E6kMaprnXnogkdmvyNAT4GeIZXyoeBGxNGY1+L+girB7\
/UHbEUtBAxdD6CkPKX4PAAmzDIZTe5oK3PqNrHrgIcfeIeeJgfQyzumXhYVLeLBNCdEqKSkYkyVP3IppTWGdTFkzGjILaGxiwXUjmsLOo1Qs54Yo17+7XGfD1YqtXTWI4NQZxx5LDKmDSuwY0/LPMKYZgzCnKLxy\
KB8b9e3pLitRLC8dUo7y99pTBH9px56O1thTjhRf+Tzd8pYzmuyOIo6s1tnV5L9jV81fZFdZoUSrpnXCzq2To/FFcnTCcoQ4SgU7+uSE5MPeWHpiEH8gm5d53NflRsfWoWo7eY5AFo3sPgCeohkDn4CueSIiMGsr\
B/rmdCVKEniKkso1ngtWnd1za6qt6jHOqqD3qC4MtpZ+iFeCJy0qhvRyCk5n69xpTxqkyGAjuEgiVrjCvnupWq5MSBibcn8wvhg1W6bQqilit56xPrbc/ECLpY9pVOKvw4VjGegJTKKU73Fdri7OJwJ0hDNtXcZr\
L595AYu4uLMtMtvsexlg6PLpWnqi7xhsfjo9pyv0PCOHuSnvM4Sb+vQk5xRuUxzDulf3mLJN7lE25cgLEPibDx6iS3HSp0xFKkQ7RffxPfQGQfKmbIn9vgWRDkkOMNhToQ1Rv2EpH+TygMID26PkHDx2ConHPRK3\
xRRHrx2vaA1E0pK+djR7Ltyjdd2wvEC5QlkIhTHguQvpPah0JrXRUOKeK783Q1pVTfmy3MYiC4BKGivXEliP1QGPQ/ILCtd4dlHYlysySBoLtuR5DIVzTfUxLBj1dLWLekd9Xd0CneucJYt62JB1K2luJXo8vUW0\
yR0clEBL3lHJXqCXHHQv1rvscG9/sAoYiGlDwRf7PcBgkl2EBDNhCLpIrTWFYkeFQaW46yONWaFjhalW9wQYxN8wMIj8GKLh1Cz6CeN/AwtS52VnyN91qKCdxy5M7wjG6LvYZA+wkAJ2sBiUPjV8eYCRtja0kg9F\
6xwIHjDX4vSW5JmSPhxYkTHfol7gaW+ozElaxpJWYC6uJNzYCln+JwhZX7zUOniA5PM2GFSjj8KD0ocHDy+EB8Mx18oXWCi7XmueERa8WKamvkyRzhSwSRsTrNaUSJ4DCbnepkZRPJLW4RbyJE4iCCSyRFwIEm8L\
v4drEMIFunFCSVeaGy6H/QNMskyLzQkxDJ7Bwt4fZljnB867Tn7h7RkInqefLmXrlJmIWMkxI8Qaf7aUfY4qM5epspKy3k6b7TdrdJiv4spi64xC5ViFY73n039J4W+4NyFrj48UO0I5tWzBSLGrbgffiw58dCco\
w53dg2+SO1ylKuV/II1NsfckR8rgBs2bT0KqnIWmldnMy9k/PoLwagqR7pJ/vwj3YBgY7ZHtV8Up5iJ2Nzx3nnKlgzuSHSl20czK8i5LqT+qZm4f5FSwUckBgmp6x7+v8VLLZXQjxhvRjSNYLYnEE0XhpeIfknrW\
6Idg+zSuBivG5abGm/rlEcNz7ZR2UbiaN9rBB9U0EJ1HBJ1ybQiiiVckp6486yv0vtBN/IyQ5h6Nilyw2UsOJF0U4xn9JT6YadO4v7tWi+c3lIqZW0iMrU93Rfc4C0R0OFqlw2V+6B8tWDO9gjUqal9TojVzxv1z\
MvZ7hAOcr41hmD/L0da/0jLXZXOXO2JrhPRFrx4hZsqR61Jm2hlz+Ba1yEZeXrRZtfM62K1h+MbptV84MG8VaAmapMoXsGZKsqLgbdT4GG4oKJvWow+8vQLkjqNS4KPAHmWMIKUMfJBmyL6nwBbNCLt4xEVeqBHM\
o0fgg1H9bCfZ39AgXdDrNwZtkpA2v1IBLUf9tntZeS+BiNvQCu+e/uFn0h2wiNq7kI8tjtY8iC96MLzoweiiB8lFD9LeA7zIEIAW8Tmi59ONCZB6QPQucav6SacYzN/9Uw7225Z29wUcn8NcGkQKkOhWtaU8hiop\
b2/dxi+JC4cEsF/1uWAJrn+gm1TCdJ2z4vpF/9VFGEn6HTh0SsU4bEW/PINtWYVl4U/MV/PiFolqqXboNcOpKZJ73EIFRg77Lo6e0WKvWY1VHDWAdFIRuWwoKoERpz9BmGvIvoLqwi+5mK2lIUpWv/xZdqZBng32\
1GaQ4W3Ih7q2vU1GGzKWtH1wIHsTePONhgB0sbOdzTF6j1SCvzi4CW8eEhjIVK8Qb/hokxFj+fOjn4NH/+AtwhFsyTARbqV8NAi+wU/e0G4x2H1FXNgDVTniaZl8vjgMr/E7jDCMuUPhgazmjSe0YLZvgoGYeja6\
luXMCNO0QV7ZPJTuwI5R49XWY4VTDW2ZVoOewGfySdajPPbL5uQn/8Xcto15G3ToYds2vwXZjSLkjTsFRgT6MohO4upNk3zXttcZ4aH3Lg5s9lheXNt+QJWGEpHLWWvVtPPwJkjb9QDSeJCay9ptsMwEJiVstbag\
ZQ/eN6MfPZ806pebeBuHcIPMl1Ipp9qY+KLdK8gGKGPPhVQEfjrg0wAq3oJExYFf8C59RLe5oAW7RE8YQehf8MSC+BoYio1gxi5TQjtqmuLdB5jE3QdP5/MXr7wda9rxaKV4KxVFEpDPLdWdWIBcdA8owDrpfKWR\
BacdYicjSErv9ANvayHvOsEvIpYgAxzI787n2R7EXCFFY7Cv3MWiGjkcAvc7CXmyu7w9q5Vp3MonZx3k420mEtOCHsNcMzfXWkYeQXrNP+DCRCEeYRGi0xHiERbh11SVo6nK2jsIheTlhLFe5J/8Eq07BiYTmjad\
oxDiINg8nvJskQ9w/kNTdF6ESgks6Ek7t++xqvCOojhedt7IXPmOjsjdDTZUO5XMO7NGrz/A5oQQBh9v8oB2eclpM97XEem7GhwDmgbI7WPaoJYzF5tce0dOCBWNfbwEHxAKawzv4FZZKOFM75OaPyHUvQTd+ZW8\
Kwd+NNEKkaMA4Go2wk3ZH0gGclnzsWwcyu1bErpwh4QcbgQYxphCCLzBUHkFAYfGnZ5RPpnev+MO2jhgPWG/we3ZY5zskI4FcASI9uD0kopRdcU7qrV3ckdn6lX0aqN7comvtdr7G91PApe6k1fm8ynZ/ro+Ztcm\
nQnoFWcZUEB25jOLV6eBaogqe8yV8g2INTE/8FdI9xAh+Ru7ebn4i7+UWIoaXI0F96hfS/e4MQn16ZD8qoI9T4g117y4dJtW7dzkEhGYIZYXoah05SvvEApF7Rgwf7P9gAsy4vnVDZez1dHkRx5aa4y394JgKDtr\
6glvUm3kVIunewVbrmZ8JOfpkDhgfFSpzeOYR4cxkQaxmGov2/efsejmeef21HQEAjUmKYXsQYCb8fMH2d7+YGePdZKBxSOE16rLxAdy3JBb37Re7cWMpm4X+d2btHhhEeMSJyPDCxmiwFgsA+5yBUfl6OQndocz\
zsEXnK1WWPAgKUQWoxGbG2RDnbQQbMTOTYe9faDDMOYqKa6aPbym9fAgzmAADNcP233HZvV0jcxIeb4ZWoiEX+1eB+fcAKipeA84QtH8piyey9cKDqLdNzzZJZp662AJLMpDFrjRISoXNZ9Pnm0+FjsBXwx3hlir\
MPxhIBkCZfDEDJN/twNf6ftrDHqmb3FxI85tpHjPx0elwh+gnHpS4kiVnvQ7kRcw6PzV2iF8Wk+2g/ZUANnAPrrDgiNnkYw8jFaV8hruFx9dNDJETfFnj6w3OuJSRaXFyDVcBPssGB8LQUmmrLUDhlSTW58AYPQn\
0ckt0MpnrKXeWdRC67A/2YwKoXFkph1N77QCjIev0EjkfK0ReOrDhBf+xal/sfQv3vkXH7oH5WW9g/Py/rV/qhoWY2ft2Wjf4q9he6+60R6qxqXglPB2+MXRtPBgBRAXoQqoOlB5CHPc6WjgGOL5c1C7JJFDhDWM\
M3UxQEvDirJp2EHQGIjyUmrkbh+ytDTRKz7xY62OCjkOnZGWcxW4DyTWz2mfOl/zKZ1eNZEYwO5j6OrgmeRMbsqrBZ+v0+AsX7gtE1Ui5/jQPkrcuoXwX/ZwwXFmlZjjIt4mi6mLo18lR6dbFVytTK9whS+243cc\
4DbuBJhXHGlNJDExkT2S11l8iwPoaXhrvrgj0UwkS6/rlQPAHvPxFo0LM9hRP+VYRYHHMoza+5D/gQMUTG+0UuiMtygXjqFxKNEDDwTVSHP6pYhQnIntjFzddVW75F4tRJVtq7bzae0dChetoWHZTgDRNx9IRue5\
PKZtfnL4jybu3KV5lphXdQlfiEyOgiOFkZIhoy2FkT8nH/eTQbs/7cDf9owYnLVzmW8dhKGccHeLO8eKSf/4vs5pfLGHqXCYkLYggOSdvVfKHsDuUW2YZlzAqRJF682fyzE37QQnHCtoXKTIStAUY//fpJ5uVSrY\
YC2Ulh6rhnzuSi019JqPxGxal/KTYQJ+q/ta6ZOUUS12QNSPkW2BXps+hRr9tt06yRlZSTYbjsK3ixsXUN1dQNka+NQgBdtB3OIm1MOAv8lXv6k4OltJgEsdPwBrH77ng/Y8fcqtjFZk5XxFUGixki5hrejQJrIU\
kpx6+fsY5cDBoRhPhODfMxIpnTTlZinOGfr3FDLFdra4yHK0tck7mdqiialgG9hGE+1iEmWHDjTy/Hn/TYNvtjucqDOKJHcGLe9X6953MK/9hsqZ8PLqXoDn7P7j7bJYwGm7WqXDNFcWkton9Zvl4lf/5tDerIpl\
Icfy+ufQKjmBaegFU2KvlIGTBJJl0ozotRo/aH+58mJ78YTrQdT4V0mBjin2z7e5up8uDrni3X/7znzJL5ph+9Oi5De99/z2cXdRuXK7wQga/gQRxINbEIM0su3qgvbKas0LlJHHNaDGvOmNxslOBNGCdxraiyXX\
8q/vZX3PWFE16t1+0f66y3KCk648otZl29n/tFTDQjGib9nebJK2h/EnDuvzf/HOm0yGmrfdIzgYeRedoEU/LNw/zqa3Q3Vl12LnpCx3pDH+9c4+1r2+cSeWb/eUf76ru+gc4Vf0DrLutWn0muOpde/9/pHVUe86\
7l0Pe9dJ7zrrXZvute6Np7OhWAe9/IK7GPsXJ6vHZ/9lf/qS6+gzZegymbpMxvrXySXX6SXX2Uevlx+5evORq+452+uuzUevFx9bO5f+fe66TT6LRsvPmHd/5M0lWqA3ct0bie5RUXfa2/AvrvkXnWZv+Be3/Ysn\
/kWHIW97mqY3zqJ3bXrXdbxmlej/4ir+q7XAH9USf1SL/FEt80e10GXXn/mnlYuBtSswxZVHWzZHvNKG7eE6C6YaxyPalaYv/t8yrM70KqNVH9zGSZaPVPbb/wLL+NGn\
""")))
ESP8266ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
eNrNXXlj1Eay/yrS2BjbmKRbmtFhIJkZzAQI7IKJHUgmWUstCcID1h5m14Ql3/11XeqWZowhx773h8no6qOquupXR3f+c3VZv1te3Q/Kq/N3RTZ/p9X8nVJj+4+ev2sa+JtN4Fb3L7N/Tf313+9O7tnvhjG897V9\
ZOxViY+4uRyaHNMT+vik15pe/1t779A4Vkfh3+cRzd/ltqcyljEo78I2edVv4F80PhX7U/B/ed+Wbo7cGbUR7HjDsRPOKvzgqTegIpNP8yxpf9k/IVQ2lNvwjS5di3b4i960s7bn+VJ+PrL/1N6FjrwmjPReKvml\
m3bUN+0bOY9DtcPLzMgbkfJGpNwTM2wbtk2OPDroHrt8juCYSv9Cui9BRBoWvyzzLgp38RS/Gu89wP+oG/ifd3dFaNV9/lUO7/EvY77gX9p2UEd8UWU5/nrR3rONVNJjbgdWozSOH2zJkLjJ0LbJwpfbLwtNwgqf\
aA3PBsXGgEQPZx8Vt+3dqJja9qNiAv0VtrkmKr4mka9Tas20fLZdlMgL+7Tkp7iCLMmBSW6hTJE3A+gAHqf23ybh3jMThMxBY4eQWRYV0JCG5rU0z8yC76uIBMxY4YJWXwWuW2UOqd+qWDPawsBNpobSbRPAmEgN\
g/YGED3ag3+4tWG/tYvu25sFyt5Efjy2P5BKZ/KDhxuVPBBuzDRrGjOJ3KTJbmxY/iVRl9j8EMgDz+E2LC6+PTUbgwkIxoC/0NPHt/HOaFoMWD50Jk/jSMYHXBmAuKhB0Ezny+29ts1teD4oBsxDw1MoTX8KwmQ7\
Sl1wF1l8x95l0jbSXTzw+6V2tA7gRzAgPQcC3FhBK2HA9r9qRIpUae6mrnkc0QXjaAeqVhkKpK5qlhAiFP3XCpzVyHlMY4PXMtQjafS4kQHbmzkrtyZ5u9Hgy7Of5M7t+ZtmQ159wH3CN5WvOJvb+NUZ/n7idRe7\
EeZZV2XlncGp5D2NDJZI89ZrQkxiwi+DpqKvZu88Bei1NnsN92f2G9aS2vQIkVNf2w1pTprdWF6GG3Ygb6jlpjfOLxwRstR9ov0BTOX+wLv5TEYVeXytNLyh4z3b4VLuKboHwg2j/a0nC122ZskV/1ncfca/Rz6t\
dAVqG+wUknhO8qiS1uA1TDqSA3x25uuP96syWFu1VVck1Rp7ft1a0j1AOPq8/9ExL+CCNGMFph1n/wW9lZmHAcjg8PgJmDBWjRFYjgmrkYSVp8MLsOxgwPqfK90dEj1rRX0Z7OtL/pF+RXOAPtBgrTZN03h+0TSS\
tdOwT4uKhm+S7x0PAFDA67S2t1qCPxVpN0x5YUjZCEsL4cmNlUdf0yOT/M3n9pa8MnsIt7MHrJXWjiUS2fOW/OwGdwnNDblHHX1WQzPRBPvUFtBJDbvgNySZbC0EMoLBVttuQhbdLWaELNkeYI5DEhA0SCA6AMmM\
U6HcTA6WAhdAJuq3mbme6uL21DEf8GJdjweowb+A9g95dKNSDNmUf6C6OgLtL4o4PTlCs3MANx8dBPACDFyP4wBhhZJpaZlzgIvYDnJ2zaOLYnPqyODRRifxfJlF3tPsmDVbFrEuQuKYJHAaKyM10ggdA8dkhLso\
O7OglcG/owhdEemjldsRQJVsiQD2PA/+WrTVaN0iIHWl085nrehueP1iyxPmce3z/B3jCpN2JaYx/9RkZRu/z/wF+SdNmuzB5wHId3dMeSsroJHoGjEijnPXXuQMp7NvB3SlRrvfB/QWIlkwanXzjPElukQzdDxG\
raLluY+8dVY5Gq2Sk5SUYGAZLwqICkCPjxYMfvHSjM48sCFYQnzQji5rQDWWLeKSXgC96MhKTIwqYCoMR2tlJ9aU3h2YwnALBXS2jT6u46s2GylR0T60XYEMDSMxbNjLLbaoccq+FrY74MGuyAg4DBkxFmcUs7pt\
X8j24BXA+bWaTHY3+T3Vf+8WdHV9LpSr+8+BfLbxOuMXiv4LLJ4j3z8bIBpHTB5P4d/h0/n8zr+giRkDQ3x3PZqMEUrGAQghzAt1BkujGv3AfEwAq3Q9+I+DYnZokAROFxbXWPRqRg5oA8X9qB8Tt2DKZTRgydPi\
bpYsKPEAFni0CK+VxRXCq2xtr6bi6vBqivCFCLwNM/pWAHA4KojOZPJ/PPmWTXRxAL7yEoQnvHZY7CyKvfH37BwW5HvBAsVFlPwT+rK2uixFvb3h9QcQANfxHnx7CP+Otl/hcLbgdrF5WOzefAIa8wMsM3hh+AJU\
CKjLMnZyjqGEoSZbZGULl9c2PUdaRCyemYgnGwmkQPwL9PYLdJyD6OfkWhTp1zlBKZWUxWZZbJ3Yp0mwCIGuZgP0joZG04YaBcSFxhCN873yJ4oomIqc+ixx7laRkjqtYcGRxx/+Sq3AXEwDqgxWJQ5S5YRVOy0N\
RVabrtn3vkcPfPM13a+RqmjsaxjAzWszz3GRliOa3JVHGCILX7mZqfhZOyOB3u00EjeNF71p5ILh4n5cSxaECivvG4PfhCXfAoGPIcoUvWCVr67A2nk5mBbqsBiWxZfALhBTEmCQ3cysUQjI6mmoDsNhGeJHYUxi\
TuuuJnc9aEiSjfn3o2Ao6zML0Il69B04veWReMhnT1meMDKEfgu65M9TjzGj8dhKTk64YnnC04jVLwFQdsZtJSvsCGfQ+N7tnOg+o2BBl47MkSa5NUam7rCN8h9Sayy2gwDRoCKmYjDFxOEN6CkvRXapEbQIscfl\
SNg6kNlxD6o1iwMXASVu8u9qLHob/PEasFVWsjgCjmwDnGeaKGrN5eYOBIWCcLJDRgP8hTqekJWFSTXVMTBhA23tJiqF6gaSYfNCMjgZHwTbHH01T47JvjWFv7i8mWfrZz7z0cDvmHrWmTpPg4NpY54wcEp/gGEH\
9JFWTn/p5CEBlQbEs8px8hsfmXzeTn5HWjLHZHua4ezTZ/4HeY4BWLS4IQG4puboYlO/HOwPQNimZJxaZrPHWGcTmXtXodiZTz5V+jVaEYRYuZEI0mLH0PdlTSxxWjqk/ptqQsakqVuF93JwfyA0ojFzxw6bTqin\
pnoZ348Ht+GdltQhSwC0DOqyqVq1CC0LFYSwGsbTJDMP43GgKtOAl9D8qywHnoCxyxTFwDAAprIbGNXZ9xGIJrI2lRpgtAOxRsIw2KwQcu8ti60Xeifhu4ksuPLpwnczPiZLWyf80bDPUTEvf5niaZRbfbU6XS7A\
SLZi5mTP80qVunl7RlFEFa3qlh2KRpUjatzOGVyxEqd/RwZ45EKsBA4dNKgUOsYnmxi0u0qhO2gRGVL1QnfWf0EQ1RvJItw5d2NQrSR62m8PURSmWaLZewfp13BujwcBSyNbw1fkk6GsQo4UMOo9/PMIf55TNFVp\
CJ9F5xTyp6vkOqgvgPsGFFlKBn2B8Ktn06ucXaJWQBZhJLacrDhYdOjXvD86bTjmA7LZZBytgPFGdrEvZn03rjcjzO/FRDny7bacB5QloZOpwXNYR3uCz2ExVtPn5KLRp6OPTApTS/1JSSgk2z0HSMvzdlO0M7bz\
BsqlU+4jm94W0YrPGQaDs2uiU0rViYTlw6mERMsBu39NOpA0gqR5gMtm2fd3p3fbT2mVZZk0MYIvwWyjcsk4Sp9Ke83u3cWB+5jhO8YH0R3QHoYF6mZIl5eQHOBl5xn3K5+OcSgjx2rGmP8zNYMubBMuiJUERb3Z\
TU75ATQVYVOAu/R4xvwFatXog6rABU3XAIW7KIg/QnP342ALPockEQRq0HSUSYI6oHEjsd4wDvsQAogrSDrpC6hwyYqgj6FnLDV+1jq5dblNWIPGAOUdk4Ux0f8DyxD+De3zrb5IWpKrzd3NybdEIodKndluIasl\
foikhNWt45Sdem1iZA+qGnBY9dltnzOnC6AQrvLx6Tsw2wvAwk/BLdEH4v5Yh1n7rFsUqNr1j6u8s+p5fnWCKoVmvrvjha+UPu5/AkqnqRYhtohj2p1fnVK0GTNC+vFqL5ap2kU7IN9kMpQX+ALibpjQi7ZJMK2n\
fx0n8cWqX5b4wXenI+dXdzFBFfsKCdeMmm6IuB9MDf20w/mCbCjoqpoiH0tSrZpVrNLX58uHWGpgiCHAuwzDPguktr2y7kGe4oSWdJXB15CUbAhPoQLeId7nxQFnteqRi7U0yaZLC4L1zVn3OcVAUZTcixflaoOU\
esZxUK0+EGrVyQ5n4y8w3XFIbk1jcsakGPeMfFpChymnw4SiKI3oCmdA1bseSEmnRdLS17ZQZKdpwDF+raMijcJkGqbY/nARJlGxPY6DaZidnuFKOFgUybTIviHJqDgsgiNIU3V6l5miDlzAfjzW02Lbuac4xIzz\
hGAsCojh0eCndkbjt9DANNwGNsXT7+FqwcEsTP+CO8n00I18pU7BQI7P8VtmNUYCqgG28BBT1hwRqFU+EYIw+bFEIbIzP4WZnx7AogA+peNvkM5wB1u2fvzSzgf6GEq0AZaUHfDgO1Ty0zYyWC9CpPa5pZr9qfTE\
Uhh0gWntW0pjLctFmEJ/2SmSnvL6KlO8XHMcxBjF6DSmueXRE6ca89xfKzp38fCykjqQ8PrWjrtfpC4nnFXOPIDurjjNTu9K/hkC9TDyIhnIox2JHcfkldWoqIZnnLAzuxunAxjtwAPMtNwCWEi5pFZ1wDEW+1pK\
Y1aeGmplB1mmlvjVVUbG6ExdcZNpS4EMYQeazA4tVyxZMR8IWHpGGOppNNWVjEE2h/dxLcdE7MhFB0Hm61hil9NrFhEBBkZMx5UvTSI+KAQzVAeHXWZC0W2L2a3P/4tuvWN95DmoqedcpCvBv6mrlMjK650+Ylfd\
wqhoE3vdCKjjazQqMbwYjEU06gnRf3wJinwJQm2lApEg1Igq19A2aBSK5bd2U5PCx2oNXKvMfl0KNBk6GQBGtDIwQBPRirDo9SqB9CXqlJhTY1IApQYUAEfPUcITGNLvYD0vfZ4DwbUOAWYaDTkIQ2GUHJGIBA4M\
ZaoX0jA6KZiPUc4ggW1UZA2y+GSnXSYZLR8UrvT1HFzly9woSh7NfkTw+5qol+G0Miz8odRHi6gGBQfxvr40iLcSx9Jm45hEIYtXMWMr9+klgTxP6A27DEovws1V2XdypzISx/Nb0En4jOZJ7LOz3WRapwwVPNt1\
Dg2t0gFGdA5cPoe57Z6HgAnNJENR3ro/kArJjjQQOCCB4Ca1EcwGQCSfL/W3KBkH+wcR0Udf4nb/THNx2M4iNHK73zc99N/1Ds424csp+mEaHT4d7RJ3E6kMaprnXnogkdmvyNAT4GeIZXyoeBGxNGY1+L+girB7\
/UHbEUtBAxdD6CkPKX4PAAmzDIZTe5oK3PqNrHrgIcfeIeeJgfQyzumXhYVLeLBNCdEqKSkYkyVP3IppTWGdTFkzGjILaGxiwXUjmsLOo1Qs54Yo17+7XGfD1YqtXTWI4NQZxx5LDKmDSuwY0/LPMKYZgzCnKLxy\
KB8b9e3pLitRLC8dUo7y99pTBH9px56O1thTjhRf+Tzd8pYzmuyOIo6s1tnV5L9jV81fZFdZoUSrpnXCzq2To/FFcnTCcoQ4SgU7+uSE5MPeWHpiEH8gm5d53NflRsfWoWo7eY5AFo3sPgCeohkDn4CueSIiMGsr\
B/rmdCVKEniKkso1ngtWnd1za6qt6jHOqqD3qC4MtpZ+iFeCJy0qhvRyCk5n69xpTxqkyGAjuEgiVrjCvnupWq5MSBibcn8wvhg1W6bQqilit56xPrbc/ECLpY9pVOKvw4VjGegJTKKU73Fdri7OJwJ0hDNtXcZr\
L595AYu4uLMtMtvsexlg6PLpWnqi7xhsfjo9pyv0PCOHuSnvM4Sb+vQk5xRuUxzDulf3mLJN7lE25cgLEPibDx6iS3HSp0xFKkQ7RffxPfQGQfKmbIn9vgWRDkkOMNhToQ1Rv2EpH+TygMID26PkHDx2ConHPRK3\
xRRHrx2vaA1E0pK+djR7Ltyjdd2wvEC5QlkIhTHguQvpPah0JrXRUOKeK783Q1pVTfmy3MYiC4BKGivXEliP1QGPQ/ILCtd4dlHYlysySBoLtuR5DIVzTfUxLBj1dLWLekd9Xd0CneucJYt62JB1K2luJXo8vUW0\
yR0clEBL3lHJXqCXHHQv1rvscG9/sAoYiGlDwRf7PcBgkl2EBDNhCLpIrTWFYkeFQaW46yONWaFjhalW9wQYxN8wMIj8GKLh1Cz6CeN/AwtS52VnyN91qKCdxy5M7wjG6LvYZA+wkAJ2sBiUPjV8eYCRtja0kg9F\
6xwIHjDX4vSW5JmSPhxYkTHfol7gaW+ozElaxpJWYC6uJNzYCln+JwhZX7zUOniA5PM2GFSjj8KD0ocHDy+EB8Mx18oXWCi7XmueERa8WKamvkyRzhSwSRsTrNaUSJ4DCbnepkZRPJLW4RbyJE4iCCSyRFwIEm8L\
v4drEMIFunFCSVeaGy6H/QNMskyLzQkxDJ7Bwt4fZljnB867Tn7h7RkInqefLmXrlJmIWMkxI8Qaf7aUfY4qM5epspKy3k6b7TdrdJiv4spi64xC5ViFY73n039J4W+4NyFrj48UO0I5tWzBSLGrbgffiw58dCco\
w53dg2+SO1ylKuV/II1NsfckR8rgBs2bT0KqnIWmldnMy9k/PoLwagqR7pJ/vwj3YBgY7ZHtV8Up5iJ2Nzx3nnKlgzuSHSl20czK8i5LqT+qZm4f5FSwUckBgmp6x7+v8VLLZXQjxhvRjSNYLYnEE0XhpeIfknrW\
6Idg+zSuBivG5abGm/rlEcNz7ZR2UbiaN9rBB9U0EJ1HBJ1ybQiiiVckp6486yv0vtBN/IyQ5h6Nilyw2UsOJF0U4xn9JT6YadO4v7tWi+c3lIqZW0iMrU93Rfc4C0R0OFqlw2V+6B8tWDO9gjUqal9TojVzxv1z\
MvZ7hAOcr41hmD/L0da/0jLXZXOXO2JrhPRFrx4hZsqR61Jm2hlz+Ba1yEZeXrRZtfM62K1h+MbptV84MG8VaAmapMoXsGZKsqLgbdT4GG4oKJvWow+8vQLkjqNS4KPAHmWMIKUMfJBmyL6nwBbNCLt4xEVeqBHM\
o0fgg1H9bCfZ39AgXdDrNwZtkpA2v1IBLUf9tntZeS+BiNvQCu+e/uFn0h2wiNq7kI8tjtY8iC96MLzoweiiB8lFD9LeA7zIEIAW8Tmi59ONCZB6QPQucav6SacYzN/9Uw7225Z29wUcn8NcGkQKkOhWtaU8hiop\
b2/dxi+JC4cEsF/1uWAJrn+gm1TCdJ2z4vpF/9VFGEn6HTh0SsU4bEW/PINtWYVl4U/MV/PiFolqqXboNcOpKZJ73EIFRg77Lo6e0WKvWY1VHDWAdFIRuWwoKoERpz9BmGvIvoLqwi+5mK2lIUpWv/xZdqZBng32\
1GaQ4W3Ih7q2vU1GGzKWtH1wIHsTePONhgB0sbOdzTF6j1SCvzi4CW8eEhjIVK8Qb/hokxFj+fOjn4NH/+AtwhFsyTARbqV8NAi+wU/e0G4x2H1FXNgDVTniaZl8vjgMr/E7jDCMuUPhgazmjSe0YLZvgoGYeja6\
luXMCNO0QV7ZPJTuwI5R49XWY4VTDW2ZVoOewGfySdajPPbL5uQn/8Xcto15G3ToYds2vwXZjSLkjTsFRgT6MohO4upNk3zXttcZ4aH3Lg5s9lheXNt+QJWGEpHLWWvVtPPwJkjb9QDSeJCay9ptsMwEJiVstbag\
ZQ/eN6MfPZ806pebeBuHcIPMl1Ipp9qY+KLdK8gGKGPPhVQEfjrg0wAq3oJExYFf8C59RLe5oAW7RE8YQehf8MSC+BoYio1gxi5TQjtqmuLdB5jE3QdP5/MXr7wda9rxaKV4KxVFEpDPLdWdWIBcdA8owDrpfKWR\
BacdYicjSErv9ANvayHvOsEvIpYgAxzI787n2R7EXCFFY7Cv3MWiGjkcAvc7CXmyu7w9q5Vp3MonZx3k420mEtOCHsNcMzfXWkYeQXrNP+DCRCEeYRGi0xHiERbh11SVo6nK2jsIheTlhLFe5J/8Eq07BiYTmjad\
oxDiINg8nvJskQ9w/kNTdF6ESgks6Ek7t++xqvCOojhedt7IXPmOjsjdDTZUO5XMO7NGrz/A5oQQBh9v8oB2eclpM97XEem7GhwDmgbI7WPaoJYzF5tce0dOCBWNfbwEHxAKawzv4FZZKOFM75OaPyHUvQTd+ZW8\
Kwd+NNEKkaMA4Go2wk3ZH0gGclnzsWwcyu1bErpwh4QcbgQYxphCCLzBUHkFAYfGnZ5RPpnev+MO2jhgPWG/we3ZY5zskI4FcASI9uD0kopRdcU7qrV3ckdn6lX0aqN7comvtdr7G91PApe6k1fm8ynZ/ro+Ztcm\
nQnoFWcZUEB25jOLV6eBaogqe8yV8g2INTE/8FdI9xAh+Ru7ebn4i7+UWIoaXI0F96hfS/e4MQn16ZD8qoI9T4g117y4dJtW7dzkEhGYIZYXoah05SvvEApF7Rgwf7P9gAsy4vnVDZez1dHkRx5aa4y394JgKDtr\
6glvUm3kVIunewVbrmZ8JOfpkDhgfFSpzeOYR4cxkQaxmGov2/efsejmeef21HQEAjUmKYXsQYCb8fMH2d7+YGePdZKBxSOE16rLxAdy3JBb37Re7cWMpm4X+d2btHhhEeMSJyPDCxmiwFgsA+5yBUfl6OQndocz\
zsEXnK1WWPAgKUQWoxGbG2RDnbQQbMTOTYe9faDDMOYqKa6aPbym9fAgzmAADNcP233HZvV0jcxIeb4ZWoiEX+1eB+fcAKipeA84QtH8piyey9cKDqLdNzzZJZp662AJLMpDFrjRISoXNZ9Pnm0+FjsBXwx3hlir\
MPxhIBkCZfDEDJN/twNf6ftrDHqmb3FxI85tpHjPx0elwh+gnHpS4kiVnvQ7kRcw6PzV2iF8Wk+2g/ZUANnAPrrDgiNnkYw8jFaV8hruFx9dNDJETfFnj6w3OuJSRaXFyDVcBPssGB8LQUmmrLUDhlSTW58AYPQn\
0ckt0MpnrKXeWdRC67A/2YwKoXFkph1N77QCjIev0EjkfK0ReOrDhBf+xal/sfQv3vkXH7oH5WW9g/Py/rV/qhoWY2ft2Wjf4q9he6+60R6qxqXglPB2+MXRtPBgBRAXoQqoOlB5CHPc6WjgGOL5c1C7JJFDhDWM\
M3UxQEvDirJp2EHQGIjyUmrkbh+ytDTRKz7xY62OCjkOnZGWcxW4DyTWz2mfOl/zKZ1eNZEYwO5j6OrgmeRMbsqrBZ+v0+AsX7gtE1Ui5/jQPkrcuoXwX/ZwwXFmlZjjIt4mi6mLo18lR6dbFVytTK9whS+243cc\
4DbuBJhXHGlNJDExkT2S11l8iwPoaXhrvrgj0UwkS6/rlQPAHvPxFo0LM9hRP+VYRYHHMoza+5D/gQMUTG+0UuiMtygXjqFxKNEDDwTVSHP6pYhQnIntjFzddVW75F4tRJVtq7bzae0dChetoWHZTgDRNx9IRue5\
PKZtfnL4jybu3KV5lphXdQlfiEyOgiOFkZIhoy2FkT8nH/eTQbs/7cDf9owYnLVzmW8dhKGccHeLO8eKSf/4vs5pfLGHqXCYkLYggOSdvVfKHsDuUW2YZlzAqRJF682fyzE37QQnHCtoXKTIStAUY//fpJ5uVSrY\
YC2Ulh6rhnzuSi019JqPxGxal/KTYQJ+q/ta6ZOUUS12QNSPkW2BXps+hRr9tt06yRlZSTYbjsK3ixsXUN1dQNka+NQgBdtB3OIm1MOAv8lXv6k4OltJgEsdPwBrH77ng/Y8fcqtjFZk5XxFUGixki5hrejQJrIU\
kpx6+fsY5cDBoRhPhODfMxIpnTTlZinOGfr3FDLFdra4yHK0tck7mdqiialgG9hGE+1iEmWHDjTy/Hn/TYNvtjucqDOKJHcGLe9X6953MK/9hsqZ8PLqXoDn7P7j7bJYwGm7WqXDNFcWkton9Zvl4lf/5tDerIpl\
Icfy+ufQKjmBaegFU2KvlIGTBJJl0ozotRo/aH+58mJ78YTrQdT4V0mBjin2z7e5up8uDrni3X/7znzJL5ph+9Oi5De99/z2cXdRuXK7wQga/gQRxINbEIM0su3qgvbKas0LlJHHNaDGvOmNxslOBNGCdxraiyXX\
8q/vZX3PWFE16t1+0f66y3KCk648otZl29n/tFTDQjGib9nebJK2h/EnDuvzf/HOm0yGmrfdIzgYeRedoEU/LNw/zqa3Q3Vl12LnpCx3pDH+9c4+1r2+cSeWb/eUf76ru+gc4Vf0DrLutWn0muOpde/9/pHVUe86\
7l0Pe9dJ7zrrXZvute6Np7OhWAe9/IK7GPsXJ6vHZ/9lf/qS6+gzZegymbpMxvrXySXX6SXX2Uevlx+5evORq+452+uuzUevFx9bO5f+fe66TT6LRsvPmHd/5M0lWqA3ct0bie5RUXfa2/AvrvkXnWZv+Be3/Ysn\
/kWHIW97mqY3zqJ3bXrXdbxmlej/4ir+q7XAH9USf1SL/FEt80e10GXXn/mnlYuBtSswxZVHWzZHvNKG7eE6C6YaxyPalaYv/t8yrM70KqNVH9zGSZaPVPbb/wLL+NGn\
""")))
ESP8266ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
""")))


def _main():
    try:
        main()
    except FatalError as e:
        print('\nA fatal error occurred: %s' % e)
        sys.exit(2)


if __name__ == '__main__':
    _main()
