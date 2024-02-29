# 航空保障形式化建模与验证
针对方案正确性验证中存在的航空保障系统难建模、作业执行行为难描述、形式验证工具难实现等挑战，基于分离逻辑的思想，提出一种航空保障系统的行为模型，并利用Coq证明辅助工具对作业规划方案进行形式化验证。
对应实际航空保障作业调度，将航空保障的行为建模为一种两层分离的序列化双层资源堆结构模型。该模型的核心组件是“作业资源堆”和“位置资源堆”。并且以此为基础构造了一套可用于描述作业执行行为的建模语言，并给出了其操作语义。通过将该航空保障模型形式化地实现于Coq证明辅助工具中，工具支持对实际航空保障作业规划方案的验证。
## 工具中证明系统的构建环节
事实上，我们基于分离逻辑的思想，一个可用于分析和验证航空保障模型下作业规划方案正确性的交互式Coq证明辅助工具。它涉及到构建语法、定义语义、航空保障系统计算状态五元组和推理规则等环节。这些环节与工程文件的对应关系如下
* 构建语法--language.v
* 定义语义--semantic.v
* 航空保障系统计算状态五元组和推理规则--state.v、SafeinHr.V
* 验证实例--三舰载机运行流程案例（Example_Three.v）+舰载机运行不满足约束情况案例（Example_Abt.v） 此外，还有一些支持工具开发的文件。
* 约束函数--function.v
* 基本引理--Aid.v、util.v
* 变量符号--三舰载机运行流程案例变量（CSSsVerification.v）、舰载机运行不满足约束情况案例变量（CSSsVerification2.v）
* 资源互不相等--NeqDefinition.v
工具实现共涉及10298行代码，其中包括138条定义和93条引理
## 工具开发环境
* 操作系统：Windows 11
* Coq版本：Coq 8.17.2023.08
## 工具的编译方式
### 1.下载压缩包文件到本地，并解压缩
**注意：** 解压缩后的文件路径，不可以有中文！
### 2.安装Coq8.17.2023.08并配置环境变量
* 安装Coq 下载地址：https://coq.inria.fr/download  
  完成安装后，需要配置Coq的环境变量：
* 打开环境变量
![image](https://github.com/oyoy111222/AssVerifi/assets/72786551/c4d67ad5-ae64-4351-8004-4bb13aa537b1)
* 在系统变量的Path一栏中，添加Coq的安装路径
![image](https://github.com/oyoy111222/AssVerifi/assets/72786551/16cb2dd1-59f8-4361-b1c1-915748f2cf21)
### 3.使用CoqIDE审阅相应代码



