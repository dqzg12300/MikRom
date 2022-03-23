package cn.mik;
// change mikrom
public class PackageItem{
    public String packageName;

    public String appName;

    public String breakClass;

    public String traceMethod;

    public String sleepNativeMethod;

    public String fridaJsPath;

    public boolean isTuoke;

    public boolean isDeep;

    public boolean isInvokePrint;

    public boolean isRegisterNativePrint;

    public boolean isJNIMethodPrint;

    public String whiteClass;

    public String whitePath;

    public String gadgetPath;

    public String gadgetArm64Path;

    public String soPath;

    public String dexPath;

    public boolean isDobby;

    public String dexClassName;

    public boolean enabled;

    public int port;
    //文件重定向列表，格式为:文件A->文件B,多条用换行分割
    public String rediectFile;
    //目录重定向列表,格式为:文件A->文件B,多个路径用换行分割
    public String rediectDir;
    //拒绝访问的路径,多个路径用换行分割
    public String forbids;
    //是否阻塞调用
    public boolean isBlock;

    public PackageItem(){

    }
}
