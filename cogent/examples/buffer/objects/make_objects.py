"""A generator script for creating a binary file encoding objects.

The script can be used to generate a new collection of objects
that fit into a specific buffer size.
"""

class Header:
    """Represents object header common to all payloads."""

    def __init__(self, length, ident, value, kind):
        self.length = 13 + length # 13 bytes for hdr plus payload length
        self.ident = ident
        self.value = value
        self.kind = kind # type of object (see below)

    def pack(self):
        return struct.pack('<3IB', self.length, self.ident, self.value,
                           self.kind)

class A(Header):
    """The A kind of object."""

    def __init__(self, ident, value, w):
        Header.__init__(self, 2, ident, value, 0)
        self.w = w

    def pack(self):
        hdr = Header.pack(self)
        return hdr + struct.pack('<H', self.w)

    def make(ident, value):
        w = random.randint(0, 65535)
        return A(ident, value, w)

class B(Header):
    """The B kind of object."""

    def __init__(self, ident, value, x, y):
        Header.__init__(self, 3, ident, value, 1)
        self.x = x
        self.y = y

    def pack(self):
        hdr = Header.pack(self)
        return hdr + struct.pack('>BH', self.x, self.y)

    def make(ident, value):
        x = random.getrandbits(1)
        y = random.randint(0, 65535)
        return B(ident, value, x, y)

class C(Header):
    """The C kind of object."""

    def __init__(self, ident, value, z):
        Header.__init__(self, 8, ident, value, 2)
        self.z = z

    def pack(self):
        hdr = Header.pack(self)
        return hdr + struct.pack('>Q', self.z)

    def make(ident, value):
        z = random.randint(0, 18446744073709551615)
        return C(ident, value, z)

makers = [ A.make , B.make , C.make ]

def make_object():
    ident = random.randint(1, 10000)
    value = random.randint(999, 999999)
    kind = random.randint(0, 2)

    return makers[kind](ident, value)

if __name__ == "__main__":
    import os
    import struct
    import sys
    import random

    random.seed()

    # Generate the objects
    MAXFS = 4096 # Our block is 4KiB in size
    size = 0
    objects = []
    while True:
        obj = make_object()
        if size + obj.length > MAXFS:
            break
        else:
            size += obj.length
            objects.append(obj)

    # Find the next object file
    inst = 1
    fname = "objs.bin"
    while os.path.isfile(fname):
        fname = "objs{0}.bin".format(inst)
        inst = inst + 1

    # Write binary object data to file
    with open(fname, "wb") as f:
        for obj in objects:
            f.write(obj.pack())

    print("Wrote {0} bytes to binary file {1}\n".format(size, fname))
