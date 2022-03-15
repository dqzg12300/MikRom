package cn.mik;
// change mikrom
import android.util.Log;

public class InjectDex implements IMikDex {
    private String TAG="mikrom";
    @Override
    public void onStart(String path) {
        Log.e(TAG,"InjectDex.onStart");
    }
}
