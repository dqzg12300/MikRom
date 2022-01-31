package com.android.server;
import android.app.IMikRom;
import android.content.Context;
import android.os.Build;
import android.util.Log;
import android.util.Slog;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import libcore.io.IoUtils;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.RandomAccessFile;

import android.util.Base64;
// change mikrom

public class MikRomService extends IMikRom.Stub {
    private Context mContext;
    private String TAG="MikRomService";
    public MikRomService(Context context){
        super();
        mContext = context;
        Slog.d(TAG,"Construct");
    }

    @Override
    public String shellExec(String cmd){
        Runtime mRuntime = Runtime.getRuntime();
        try {
            //Process中封装了返回的结果和执行错误的结果
            Slog.d(TAG,"shellExec data:"+cmd);
            Process mProcess = mRuntime.exec(cmd);
            BufferedReader mReader = new BufferedReader(new InputStreamReader(mProcess.getInputStream()));
            StringBuffer mRespBuff = new StringBuffer();
            char[] buff = new char[1024];
            int ch = 0;
            while ((ch = mReader.read(buff)) != -1) {
                mRespBuff.append(buff, 0, ch);
            }
            mReader.close();
            return mRespBuff.toString();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            Slog.d(TAG,"shellExec err:"+e.getMessage());
        }
        return "";
    }


    public static void writeTxtToFile(String strcontent, String filePath) {
        String strFilePath = filePath;
        String strContent = strcontent + "\n";  // \r\n 结尾会变成 ^M
        try {
            File file = new File(strFilePath);
            makeFilePath(file.getParent(),file.getName());
            if (!file.exists()) {
                file.getParentFile().mkdirs();
                file.createNewFile();
            }
            RandomAccessFile raf = new RandomAccessFile(file, "rwd");
            raf.setLength(0);

            // 写文件的位置标记,从文件开头开始,后续读取文件内容从该标记开始
            long writePosition = raf.getFilePointer();
            raf.seek(writePosition);
            raf.write(strContent.getBytes());
            raf.close();
            //
        } catch (Exception e) {
            Log.d("MikRomService","Error on write File:" + e);
        }
    }

    // 生成文件
    public static File makeFilePath(String filePath, String fileName) {
        File file = null;
        makeRootDirectory(filePath);
        try {
            file = new File(filePath +"/"+ fileName);
            if (!file.exists()) {
                file.createNewFile();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        return file;
    }

    // 生成文件夹
    public static void makeRootDirectory(String filePath) {
        File file = null;
        try {
            Log.d("FileHelper", "makeRootDirectory "+filePath);
            file = new File(filePath);
            if (!file.exists()) {
                boolean isok= file.mkdir();
                Log.d("FileHelper", "makeRootDirectory "+filePath+" "+isok);
            }
        } catch (Exception e) {
            Log.d("MikRomService", e+"");
        }
    }

    public static String readFileAll(String path) {
        File file = new File(path);
        StringBuilder sb=new StringBuilder();
        if (file != null && file.exists()) {
            InputStream inputStream = null;
            BufferedReader bufferedReader = null;
            try {
                inputStream = new FileInputStream(file);
                bufferedReader = new BufferedReader(new InputStreamReader(
                        inputStream));
                String outData;
                while((outData=bufferedReader.readLine())!=null){
                    sb.append(outData+"\n");
                }
            } catch (Throwable t) {
            } finally {
                try {
                    if (bufferedReader != null) {
                        bufferedReader.close();
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
                try {
                    if (inputStream != null) {
                        inputStream.close();
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
        return sb.toString();
    }


    @Override
    public String readFile(String path){
        return readFileAll(path);
    }
    @Override
    public void writeFile(String path,String data){
        writeTxtToFile(data,path);
    }


}
