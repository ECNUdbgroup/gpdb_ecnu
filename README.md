# gpdb_ecnu
##主要思想：
--------------------------
###工作1：增量计算

该方法核心思想是在函数执行过程中维持一个临时窗口，其中包含了此临时窗口对应的临时转移值，用于共享计算．以此来减少在顺序调用过程中重复进行的数据元组的读取和计算消耗．其中 临时窗口 是指临时产生的包含一系列元组的集合（包含了一个起始位置和一个终止位置，并且拥有其对应的临时转移值）。
关于该方法的具体介绍和示例请参考
“[1]马建松,王科强,宋光旋,张凯,王晓玲,金澈清.面向MAX/MIN优化的SQL Window函数处理[J].计算机学报,2016,39(10):2149-2160.”
--------------------------
###工作2：采样

该方法对每个窗口的数据进行采样，然后根据采样后的数据的窗口函数值来进行拟合用户所需要的窗口函数值。
关于该方法的具体介绍和示例请参考
Song G, Qu W, Liu X, et al. Approximate Calculation of Window Aggregate Functions via Global Random Sample[J]. Data Science & Engineering, 2018(2):1-12.
-------------------------------------
##修改记录：

(1)修改nodeWindowagg文件：
	(a)添加窗口聚合函数处理分支
		eval_windowaggregates_ttv_cr();
		eval_windowaggregates_ttv_cr_array();
		eval_windowaggregates_ttv_single();
		eval_windowaggregates_ttv_level();
		eval_windowaggregates_sample();
		以及其他辅助函数
	(b)修改WindowObjectData、WindowStatePerAggData结构体，添加新变量
	(c)修改ExecInitWindowAgg，添加对结构体内变量的初始化
	(d)修改ExecWindowAgg()函数，根据GUC参数enable_ttv的类型调用不同的窗口聚合函数处理分支（两个工作的处理分支还没有合并，只是用注释来来开启某个特定的优化工作）

	
(2)修改execnode.h
	(a)修改WindowAggState、PlanState结构体，添加新变量
	
(3)修改pg_list.h 
	(a)添加Tem_ListCell、Tem_List结构体
(4)修改tupelstore.c
	(a)添加opt_tuplestore_seek_ptr()，opt_tuplestore_copy_ptr()处理函数
(5)修改guc_gp.h
	(a)将enable_ttv、enable_sample参数添加到ConfigureNamesInt_gp中
