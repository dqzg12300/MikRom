# MikRom

mikrom是一个基于rom定制的逆向工具，请配合MikManager来便捷的使用。

### MikManager

https://github.com/dqzg12300/MikManager.git

### 镜像下载

> v0.0.1   链接: https://pan.baidu.com/s/1bn39KtlE8yW9A_51uAjB-w 提取码: s6ww 

### 说明

v0.0.1 是最初的版本，基于aosp10r2修改的，基本功能已完成，内核相关的部分未修改。jni部分简单打印。

v0.0.2 是优化后的版本，基于PixelExperience修改的，内核相关已修改，并且jni大部分优化了打印

本人测试手机型号为pixel XL

### 功能

> * 内核修改过反调试
> * 开启硬件断点
> * 自动弹出USB调试
> * 脱壳（黑名单、白名单过滤、更深的主动调用链）
> * ROM打桩（ArtMethod调用、RegisterNative调用、JNI函数调用）
> * frida持久化（支持listen,wait,script三种模式）
> * 反调试（通过sleep目标函数，再附加进程来过掉起始的反调试）
> * trace java函数（smali指令的trace）
