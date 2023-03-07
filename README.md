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
> aosp10r2_blueline_1.0.1线刷包 链接: https://pan.baidu.com/s/15pcX9HFHOIYLVZtnV9j13g  密码: dlsu
>
> lineageOS17.1_marlin卡刷包 链接: https://pan.baidu.com/s/1vX3jPuAwhrVPeY45af6dTA  密码: drm1
>
> aosp10r2_marlin_1.0.1链接: https://pan.baidu.com/s/1PKO3RwMl31uGzdCwbgRwpw 提取码: 6eex
>
> Aosp源码完整包 链接: https://pan.baidu.com/s/1UZBD6ZmhJ9IXPyMluHeVmw 提取码: ifgc 

### 说明

PixelExperience的版本不再更新，已迁移回aosp。后续如果更新都是在aosp版本了。

1.0.1版本修复必须勾选脱壳一部分辅助功能才能生效的bug。修复smali trace打印的bug。优化dex注入功能。

新增lineageOS卡刷包，这个版本优化了一下debuggable控制开关，不过修改这个设置后需要重装app生效

### 常见错误

如果使用1.0.1的mikrom要使用对应的1.0.1的mikmanager，否则无法正常脱壳。 

### win刷机

很多人说blueline在windown下刷机有问题，所以我做了个视频介绍怎么在win下刷机，b站地址贴在最后面了。

### 修复说明

aosp10r2_marlin_1.0.1重新更新了下载地址，修复了一些人反馈安装面具出现提示`Magisk is installed to external storage.`

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
> * 注入dex（实现免root的xposed）

### 原理

[FartExt超进化之奇奇怪怪的新ROM工具MikRom](https://bbs.pediy.com/thread-271358.htm)

### 视频介绍

[MikRom编译简单说明](https://www.bilibili.com/video/BV1fY411J7vp/)

[MikRom简单使用脱壳演示](https://www.bilibili.com/video/BV1vb4y1x73Q?spm_id_from=333.999.0.0)

[MikRom的注入功能](https://www.bilibili.com/video/BV1tL411N7w1?spm_id_from=333.999.0.0)

[MikRom内置的frida-gadget使用](https://www.bilibili.com/video/BV1RS4y137p1/)

[MikRom函数睡眠和smali指令trace](https://www.bilibili.com/video/BV11r4y1i7cy/)

[MikRom的dex注入Sandhook来实现免root下的xposed](https://www.bilibili.com/video/BV1k34y1t7Q3/)

[window刷机问题](https://www.bilibili.com/video/BV1id4y1F7GS/)


交流群

![qun](./qun.jpg)
=======
