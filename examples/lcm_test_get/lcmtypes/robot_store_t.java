/* LCM type definition class file
 * This file was automatically generated by lcm-gen
 * DO NOT MODIFY BY HAND!!!!
 */

package lcmtypes;
 
import java.io.*;
import java.util.*;
import lcm.lcm.*;
 
public final class robot_store_t implements lcm.lcm.LCMEncodable
{
    public long utime;
    public String command;
    public float value;
 
    public robot_store_t()
    {
    }
 
    public static final long LCM_FINGERPRINT;
    public static final long LCM_FINGERPRINT_BASE = 0xaf426bc702618f50L;
 
    static {
        LCM_FINGERPRINT = _hashRecursive(new ArrayList<Class<?>>());
    }
 
    public static long _hashRecursive(ArrayList<Class<?>> classes)
    {
        if (classes.contains(lcmtypes.robot_store_t.class))
            return 0L;
 
        classes.add(lcmtypes.robot_store_t.class);
        long hash = LCM_FINGERPRINT_BASE
            ;
        classes.remove(classes.size() - 1);
        return (hash<<1) + ((hash>>63)&1);
    }
 
    public void encode(DataOutput outs) throws IOException
    {
        outs.writeLong(LCM_FINGERPRINT);
        _encodeRecursive(outs);
    }
 
    public void _encodeRecursive(DataOutput outs) throws IOException
    {
        char[] __strbuf = null;
        outs.writeLong(this.utime); 
 
        __strbuf = new char[this.command.length()]; this.command.getChars(0, this.command.length(), __strbuf, 0); outs.writeInt(__strbuf.length+1); for (int _i = 0; _i < __strbuf.length; _i++) outs.write(__strbuf[_i]); outs.writeByte(0); 
 
        outs.writeFloat(this.value); 
 
    }
 
    public robot_store_t(byte[] data) throws IOException
    {
        this(new LCMDataInputStream(data));
    }
 
    public robot_store_t(DataInput ins) throws IOException
    {
        if (ins.readLong() != LCM_FINGERPRINT)
            throw new IOException("LCM Decode error: bad fingerprint");
 
        _decodeRecursive(ins);
    }
 
    public static lcmtypes.robot_store_t _decodeRecursiveFactory(DataInput ins) throws IOException
    {
        lcmtypes.robot_store_t o = new lcmtypes.robot_store_t();
        o._decodeRecursive(ins);
        return o;
    }
 
    public void _decodeRecursive(DataInput ins) throws IOException
    {
        char[] __strbuf = null;
        this.utime = ins.readLong();
 
        __strbuf = new char[ins.readInt()-1]; for (int _i = 0; _i < __strbuf.length; _i++) __strbuf[_i] = (char) (ins.readByte()&0xff); ins.readByte(); this.command = new String(__strbuf);
 
        this.value = ins.readFloat();
 
    }
 
    public lcmtypes.robot_store_t copy()
    {
        lcmtypes.robot_store_t outobj = new lcmtypes.robot_store_t();
        outobj.utime = this.utime;
 
        outobj.command = this.command;
 
        outobj.value = this.value;
 
        return outobj;
    }
 
}

