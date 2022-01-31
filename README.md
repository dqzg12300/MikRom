# MikRom

mikrom是一个基于rom定制的逆向工具，请配合MikManager来使用。

### MikManager

https://github.com/dqzg12300/MikManager.git

### 镜像下载

> 链接: https://pan.baidu.com/s/1g-ueGZIA2gxxKNV3VVD3bQ  密码: sp8u

### 说明

本人测试手机型号为pixel XL，代号是marlin

### 功能

> * 内核修改过反调试
> * 开启硬件断点
> * 自动弹出USB调试
> * 脱壳（黑名单、白名单过滤、更深的主动调用链）
> * ROM打桩（ArtMethod调用、RegisterNative调用、JNI函数调用）
> * frida持久化（支持listen,wait,script三种模式）
> * 反调试（通过sleep目标函数，再附加进程来过掉起始的反调试）
> * trace java函数（smali指令的trace）
> * 内置dobby注入
> * 支持自行切换frida-gadget版本
> * 注入so
> * 注入dex（实现对应的接口触发调用。目前仅测试使用）

### 原理

[FartExt超进化之奇奇怪怪的新ROM工具MikRom](https://bbs.pediy.com/thread-271358.htm)
