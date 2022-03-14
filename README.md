# MikRom

mikrom是一个基于rom定制的逆向工具，请配合MikManager来使用。

### MikManager

https://github.com/dqzg12300/MikManager.git

### 下载

> PixelExperience_marlin卡刷包 链接: https://pan.baidu.com/s/1g-ueGZIA2gxxKNV3VVD3bQ  密码: sp8u
>
> aosp10r2_marlin线刷包 链接: https://pan.baidu.com/s/1NrGRy7l5sb4nhgYgIOLrPA 提取码: f7gh 
>
> aosp10r2_sailfish线刷包 链接: https://pan.baidu.com/s/1LIdFa8vSJEmQbqXq5X7AjA  密码: q6q1
>
> Aosp源码完整包 链接: https://pan.baidu.com/s/1UZBD6ZmhJ9IXPyMluHeVmw 提取码: ifgc 

### 说明

PixelExperience的版本不再更新，已迁移回aosp。后续如果更新都是在aosp版本了。

### 编译说明

在[谷歌官网](https://source.android.com/setup/start/build-numbers?hl=zh-cn)找到你设备应该使用的对应版本

在[谷歌官网](https://developers.google.com/android/images#bullhead)下载你要刷的版本

在源码根目录下解压并执行

然后记得给我新增的目录添加下白名单

`build/core/tasks/check_boot_jars/package_whitelist.txt`添加`cn\.mik`

最后编译

`make update-api -j12`

`make -j8`

### 刷机说明

卡刷包直接使用twrp-marlin的版本刷入即可。

线刷包先到官网下载[官方rom](https://dl.google.com/dl/android/aosp/marlin-qp1a.190711.020-factory-2db5273a.zip)，解压后，将我的压缩包改名覆盖里面的image的压缩包，最后运行flash-all.sh即可

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

### 视频介绍

[MikRom简单使用脱壳演示](https://www.bilibili.com/video/BV1vb4y1x73Q?spm_id_from=333.999.0.0)

[MikRom的注入功能](https://www.bilibili.com/video/BV1tL411N7w1?spm_id_from=333.999.0.0)

[MikRom内置的frida-gadget使用](https://www.bilibili.com/video/BV1RS4y137p1/)

