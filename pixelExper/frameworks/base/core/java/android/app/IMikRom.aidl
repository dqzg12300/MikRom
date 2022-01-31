package android.app;
// change mikrom
interface IMikRom
{
    String readFile(String path);
    void writeFile(String path,String data);
    String shellExec(String cmd);
}