using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.IO;
using System.Text;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

// Bounded reader for the ELF64 DWARF unwind/LSDA encodings used by ARM64 IL2CPP.
// Unsupported or malformed metadata must disable recovery, not invent handlers.
internal sealed class ElfExceptionTable(ElfFile binary)
{
    internal record Site(ulong Start, ulong End, ulong Landing, long Selector);
    internal readonly List<Site> Sites = [];
    private ulong _position;
    private ulong _dataBase;
    private ulong _function;

    internal static ElfExceptionTable? Read(ElfFile binary, ulong method, int length)
    {
        if (binary.IsBigEndian || binary.PointerSizeBytes != 8) return null;
        var reader = new ElfExceptionTable(binary);
        try { return reader.ReadMethod(method, length) ? reader : null; }
        catch (Exception e) when (e is InvalidDataException or ArgumentException or OverflowException or IndexOutOfRangeException)
        { return null; }
    }

    private bool ReadMethod(ulong method, int length)
    {
        if (binary.GetSectionByName(".eh_frame_hdr") is not { } header) return false;
        _dataBase = _position = header.VirtualAddress;
        if (Byte() != 1) return false;
        var frameEncoding = Byte(); var countEncoding = Byte(); var tableEncoding = Byte();
        Encoded(frameEncoding);
        var count = Encoded(countEncoding);
        if (tableEncoding != 0x3b || count == 0 || count > (header.Size - (_position - _dataBase)) / 8) return false;
        var table = _position;
        ulong low = 0, high = count;
        while (low < high)
        {
            var mid = (low + high) / 2;
            _position = table + mid * 8;
            if (Encoded(tableEncoding) <= method) low = mid + 1; else high = mid;
        }
        if (low == 0) return false;
        _position = table + (low - 1) * 8;
        if (Encoded(tableEncoding) != method) return false;
        var fde = Encoded(tableEncoding);
        _position = fde;
        var size = UInt32();
        if (size is 0 or uint.MaxValue || size > 0x10000) return false;
        var end = checked(_position + size);
        var ciePointer = _position;
        var cie = checked(ciePointer - UInt32());
        var fdeData = _position;
        _position = cie;
        var cieSize = UInt32();
        var cieEnd = checked(_position + cieSize);
        if (cieSize > 0x10000 || UInt32() != 0) return false;
        var version = Byte();
        if (version is not (1 or 3)) return false;
        var augmentation = Text();
        if (!augmentation.StartsWith("z", StringComparison.Ordinal)) return false;
        Leb(); Leb(true);
        if (version == 1) Byte(); else Leb();
        var augmentationSize = Leb();
        var augmentationEnd = checked(_position + (ulong)augmentationSize);
        byte fdeEncoding = 0, lsdaEncoding = 0xff;
        foreach (var ch in augmentation.AsSpan(1))
            switch (ch)
            {
                case 'R': fdeEncoding = Byte(); break;
                case 'L': lsdaEncoding = Byte(); break;
                case 'P': Encoded(Byte()); break;
                default: return false;
            }
        if (_position > augmentationEnd || augmentationEnd > cieEnd || lsdaEncoding == 0xff) return false;
        _position = fdeData;
        _function = Encoded(fdeEncoding);
        var range = Encoded((byte)(fdeEncoding & 15));
        if (_function != method || range == 0 || range > (ulong)length) return false;
        var fdeAugSize = Leb();
        var fdeAugEnd = checked(_position + (ulong)fdeAugSize);
        var lsda = Encoded(lsdaEncoding);
        if (_position > fdeAugEnd || fdeAugEnd > end || lsda == 0) return false;
        return ReadLsda(lsda, range);
    }

    private bool ReadLsda(ulong address, ulong range)
    {
        _position = address;
        var lpEncoding = Byte();
        var lpBase = lpEncoding == 0xff ? _function : Encoded(lpEncoding);
        var typeEncoding = Byte();
        var typeOffset = typeEncoding == 0xff ? 0 : Leb();
        var typeTable = checked(_position + (ulong)typeOffset);
        var callEncoding = Byte();
        if (callEncoding is not (1 or 3)) return false;
        var size = Leb();
        if (size < 0 || size > 0x10000) return false;
        var actions = checked(_position + (ulong)size);
        while (_position < actions)
        {
            var start = Encoded(callEncoding); var length = Encoded(callEncoding);
            var landing = Encoded(callEncoding); var action = Leb();
            if (_position > actions || start > range || length > range - start || landing >= range) return false;
            var resume = _position;
            long selector = 0;
            if (action != 0)
            {
                _position = checked(actions + (ulong)action - 1);
                // Cleanup records may precede the IL2CPP managed-exception catch.
                selector = -1;
                var seen = new HashSet<ulong>();
                while (seen.Count < 16 && seen.Add(_position))
                {
                    var filter = Leb(true); var nextField = _position; var next = Leb(true);
                    if (filter > 0)
                    {
                        if (typeEncoding != 0x9c || filter > 32) break;
                        _position = checked(typeTable - (ulong)filter * 8);
                        var typeInfo = Encoded(typeEncoding);
                        if (typeInfo == 0) break;
                        _position = checked(typeInfo + 8);
                        _position = UInt64();
                        if (Text() == "22Il2CppExceptionWrapper") selector = filter;
                        break;
                    }
                    if (filter < 0 || next == 0) break;
                    _position = checked((ulong)((long)nextField + next));
                }
            }
            Sites.Add(new Site(lpBase + start, lpBase + start + length, landing == 0 ? 0 : lpBase + landing, selector));
            _position = resume;
        }
        return Sites.Count > 0;
    }

    internal Site? At(ulong pc) => Sites.Find(s => s.Start <= pc && pc < s.End);

    private byte Byte() => Bytes(1)[0];
    private uint UInt32() => BinaryPrimitives.ReadUInt32LittleEndian(Bytes(4));
    private ulong UInt64() => BinaryPrimitives.ReadUInt64LittleEndian(Bytes(8));
    private ReadOnlySpan<byte> Bytes(int size)
    {
        if (!binary.TryMapVirtualAddressToRaw(_position, out var raw) || raw < 0 || raw > binary.RawLength - size
            || !binary.TryMapVirtualAddressToRaw(checked(_position + (ulong)size - 1), out var last) || last != raw + size - 1)
            throw new InvalidDataException();
        _position = checked(_position + (ulong)size);
        return binary.GetRawBinaryContent().Slice((int)raw, size);
    }
    private string Text()
    {
        var bytes = new List<byte>();
        for (var i = 0; i < 128; i++) { var b = Byte(); if (b == 0) return Encoding.ASCII.GetString(bytes.ToArray()); bytes.Add(b); }
        throw new InvalidDataException();
    }
    private long Leb(bool signed = false)
    {
        ulong value = 0; var shift = 0;
        for (var i = 0; i < 10; i++)
        {
            var b = Byte(); value |= (ulong)(b & 127) << shift; shift += 7;
            if ((b & 128) == 0)
            {
                if (signed && shift < 64 && (b & 64) != 0) value |= ulong.MaxValue << shift;
                return unchecked((long)value);
            }
        }
        throw new InvalidDataException();
    }
    private ulong Encoded(byte encoding)
    {
        if (encoding == 0xff) return 0;
        var at = _position;
        var value = (encoding & 15) switch
        {
            0 or 4 or 12 => UInt64(), 1 => checked((ulong)Leb()), 3 => UInt32(),
            9 => unchecked((ulong)Leb(true)), 11 => unchecked((ulong)(int)UInt32()),
            _ => throw new InvalidDataException(),
        };
        value = (encoding & 0x70) switch
        {
            0 => value, 0x10 => unchecked(at + value), 0x30 => unchecked(_dataBase + value),
            0x40 => unchecked(_function + value), _ => throw new InvalidDataException(),
        };
        if ((encoding & 0x80) != 0) { var resume = _position; _position = value; value = UInt64(); _position = resume; }
        return value;
    }
}
