package cn.mik.iohook;

import android.content.Context;
import android.content.pm.ApplicationInfo;
import android.os.Build;
import android.os.Process;
import android.util.Log;
import android.util.Pair;


import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

/**
 * VirtualApp Native Project
 * change mikrom
 */
public class NativeEngine {

    private static final String TAG = "mikrom iohook";

    private static boolean sFlag = false;
    private static boolean sEnabled = false;
    private static boolean sBypassedP = false;

    private static final String LIB_NAME = "IOHook";
    private static final String LIB_NAME_64 = "IOHook64";

    public static String getRedirectedPath(String origPath) {
        try {
            return nativeGetRedirectedPath(origPath);
        } catch (Throwable e) {
            Log.e(TAG,"getRedirectedPath "+e.getMessage());
        }
        return origPath;
    }

    public static String resverseRedirectedPath(String origPath) {
        try {
            return nativeReverseRedirectedPath(origPath);
        } catch (Throwable e) {
            Log.e(TAG,"resverseRedirectedPath "+e.getMessage());
        }
        return origPath;
    }

    private static final List<Pair<String, String>> REDIRECT_LISTS = new LinkedList<>();


    public static void redirectDirectory(String origPath, String newPath) {
        if (!origPath.endsWith("/")) {
            origPath = origPath + "/";
        }
        if (!newPath.endsWith("/")) {
            newPath = newPath + "/";
        }
        REDIRECT_LISTS.add(new Pair<>(origPath, newPath));
    }

    public static void redirectFile(String origPath, String newPath) {
        if (origPath.endsWith("/")) {
            origPath = origPath.substring(0, origPath.length() - 1);
        }
        if (newPath.endsWith("/")) {
            newPath = newPath.substring(0, newPath.length() - 1);
        }
        REDIRECT_LISTS.add(new Pair<>(origPath, newPath));
    }

    public static void readOnlyFile(String path) {
        try {
            nativeIOReadOnly(path);
        } catch (Throwable e) {
            Log.e(TAG,"readOnlyFile "+e.getMessage());
        }
    }

    /**
     * @param path 只读
     */
    public static void readOnly(String path) {
        if (!path.endsWith("/")) {
            path = path + "/";
        }
        try {
            nativeIOReadOnly(path);
        } catch (Throwable e) {
            Log.e(TAG,"readOnly "+e.getMessage() + Log.getStackTraceString(e));

        }
    }

    /**
     * @param path 白名单文件
     */
    public static void whitelistFile(String path) {
        try {
            nativeIOWhitelist(path);
        } catch (Throwable e) {
            Log.e(TAG,"whitelistFile "+e.getMessage());
        }
    }

    /**
     * @param path 白名单目录
     */
    public static void whitelist(String path) {
        if (!path.endsWith("/")) {
            path = path + "/";
        }
        try {
            nativeIOWhitelist(path);
        } catch (Throwable e) {
            Log.e(TAG,"whitelist "+e.getMessage());
        }
    }

    /**
     * 禁止
     */
    public static void forbid(String path, boolean file) {

        if (!file && !path.endsWith("/")) {
            path = path + "/";
        }
        try {
            //Log.e(path);
            nativeIOForbid(path);
        } catch (Throwable e) {
            Log.e(TAG,"readOnly "+e.getMessage()+ Log.getStackTraceString(e));
        }
    }

    /**
     * 开启IO重定向
     */
    public static void enableIORedirect(Context context) {
        if (sEnabled) {
            return;
        }
        ApplicationInfo coreAppInfo;
        try {
            //coreAppInfo = VirtualCore.get().getUnHookPackageManager().getApplicationInfo(VirtualCore.getConfig().getHostPackageName(), 0);
            coreAppInfo=context.getApplicationInfo();

        } catch (Throwable e) {
            throw new RuntimeException(e);
        }

        Collections.sort(REDIRECT_LISTS, new Comparator<Pair<String, String>>() {
            @Override
            public int compare(Pair<String, String> o1, Pair<String, String> o2) {
                String a = o1.first;
                String b = o2.first;
                return compare(b.length(), a.length());
            }

            private int compare(int x, int y) {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.KITKAT) {
                    return Integer.compare(x, y);
                }
                return (x < y) ? -1 : ((x == y) ? 0 : 1);
            }
        });
        for (Pair<String, String> pair : REDIRECT_LISTS) {
            try {
                Log.e("mikrom","启动之前:"+pair.first);
                Log.e("mikrom","启动之前:"+pair.second);
                nativeIORedirect(pair.first, pair.second);
            } catch (Throwable e) {
                Log.e(TAG,"readOnly "+e.getMessage()+ Log.getStackTraceString(e));
            }
        }
        try {
            String soPath = new File(coreAppInfo.nativeLibraryDir, "lib" + LIB_NAME + ".so").getAbsolutePath();
            String soPath64 = new File(coreAppInfo.nativeLibraryDir, "lib" + LIB_NAME_64 + ".so").getAbsolutePath();

            //String nativePath = VEnvironment.getNativeCacheDir(VirtualCore.get().isPluginEngine()).getPath();//当前进程可读，可写的目录
            String nativePath =getNativePath(context);

            Log.e(TAG,"参数路径 soPath "+soPath);
            Log.e(TAG,"参数路径 soPath64 "+soPath64);
            Log.e(TAG,"参数路径 nativePath "+nativePath);

            nativeEnableIORedirect(soPath, soPath64, nativePath, Build.VERSION.SDK_INT, getPreviewSDKInt());

        } catch (Throwable e) {
            Log.e(TAG,"enableIORedirect "+e.getMessage()+ Log.getStackTraceString(e));
        }
        sEnabled = true;
    }

    public static void bypassHiddenAPI(){
        if (BuildCompat.isPie()) {
            try {
                Method forNameMethod = Class.class.getDeclaredMethod("forName", String.class);
                Class<?> clazz = (Class<?>) forNameMethod.invoke(null, "dalvik.system.VMRuntime");
                Method getMethodMethod = Class.class.getDeclaredMethod("getDeclaredMethod", String.class, Class[].class);
                Method getRuntime = (Method) getMethodMethod.invoke(clazz, "getRuntime", new Class[0]);
                Method setHiddenApiExemptions = (Method) getMethodMethod.invoke(clazz, "setHiddenApiExemptions", new Class[]{String[].class});
                Object runtime = getRuntime.invoke(null);
                if (BuildCompat.isEMUI()) {
                    setHiddenApiExemptions.invoke(runtime, new Object[]{
                            new String[]{
                                    "Landroid/",
                                    "Lcom/android/",
                                    "Ljava/lang/",
                                    "Ldalvik/system/",
                                    "Llibcore/io/",
                            }
                    });
                } else {
                    setHiddenApiExemptions.invoke(runtime, new Object[]{
                            new String[]{
                                    "Landroid/",
                                    "Lcom/android/",
                                    "Ljava/lang/",
                                    "Ldalvik/system/",
                                    "Llibcore/io/",
                            }
                    });
                }
            } catch (Throwable e) {
                Log.e(TAG,"bypassHiddenAPI error "+e.getMessage());
                e.printStackTrace();
            }
        }
    }

    public static void bypassHiddenAPIEnforcementPolicyIfNeeded() {
        if (sBypassedP) {
            return;
        }
        //Q是10
        if (BuildCompat.isQ()) {
            //Log.e("开始执行 bypassHiddenAPI");
            bypassHiddenAPI();
        } else if (BuildCompat.isPie()) {
            //P是9
            try {
                nativeBypassHiddenAPIEnforcementPolicy(
                        Build.VERSION.SDK_INT,
                        BuildCompat.getPreviewSDKInt());
            } catch (Throwable e) {
                e.printStackTrace();
            }
        }
        sBypassedP = true;
    }

    public static boolean onKillProcess(int pid, int signal) {
        Log.e( TAG,"killProcess: pid = %d, signal = %d." +pid+ "  "+  signal);
        if (pid == Process.myPid()) {
            Log.e(TAG,Log.getStackTraceString(new Throwable("killProcess == MySlef"+ Process.myPid())));
        }
        return true;
    }

    private static final String getCanonicalPath(String path) {
        File file = new File(path);
        try {
            return file.getCanonicalPath();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return file.getAbsolutePath();
    }


    public static native String nativeReverseRedirectedPath(String redirectedPath);

    public static native String nativeGetRedirectedPath(String origPath);

    public static native void nativeIORedirect(String origPath, String newPath);

    public static native void nativeIOWhitelist(String path);

    public static native void nativeIOForbid(String path);

    public static native void nativeIOReadOnly(String path);

    public static native void nativeEnableIORedirect(String soPath, String soPath64, String cachePath, int apiLevel, int previewApiLevel);

    public static native void nativeBypassHiddenAPIEnforcementPolicy(int apiLevel, int previewApiLevel);


//    @Keep
//    public static int onGetUid(int uid) {
//        if (!VClient.get().isAppRunning()) {
//            return uid;
//        }
//        return VClient.get().getBaseVUid();
//    }

//    @Keep
//    public static void onSystemExit(int code) {
//        if (!VClient.get().isAppRunning()) {
//            return;
//        }
//        VLog.w("V++", "System.exit:" + code);
//        if (VClient.get().countOfActivity > 0) {
//            VirtualCore.get().gotoBackHome();
//        }
//    }

//    @Keep
//    public static void onSendSignal(int pid, int sig, int quiet) {
//        if (!VClient.get().isAppRunning()) {
//            return;
//        }
//        VLog.w("V++", "onSendSignal:" + pid + ", " + sig);
//        //返回主界面
//        if (pid == Process.myPid() && sig == Process.SIGNAL_KILL) {
//            if (VClient.get().countOfActivity > 0) {//有前台activity才返回桌面。
//                //异常闪退的在VClient有处理
//                VirtualCore.get().gotoBackHome();
//            }
//        }
//    }


    public static String getNativePath(Context context) {
//        getNativeCacheDir(VirtualCore.get().isPluginEngine()).getPath();
        return "/data/user/0/" + context.getPackageName() + "/";
    }


    public static int getPreviewSDKInt() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            try {
                Log.e(TAG,"getPreviewSDKInt 返回结果 " + Build.VERSION.PREVIEW_SDK_INT);
                return Build.VERSION.PREVIEW_SDK_INT;
            } catch (Throwable e) {
                // ignore
            }
        }
        Log.e(TAG,"getPreviewSDKInt 返回结果 " + 0);
        return 0;
    }

}
