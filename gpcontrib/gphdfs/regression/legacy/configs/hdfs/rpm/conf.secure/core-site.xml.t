<?xml version="1.0"?>
<!--
   Licensed to the Apache Software Foundation (ASF) under one or more
 contributor license agreements.  See the NOTICE file distributed with
   this work for additional information regarding copyright ownership.
 The ASF licenses this file to You under the Apache License, Version 2.0
   (the "License"); you may not use this file except in compliance with
 the License.  You may obtain a copy of the License at
  http://www.apache.org/licenses/LICENSE-2.0
  Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
  limitations under the License.
  -->
<?xml-stylesheet type="text/xsl" href="configuration.xsl"?>
<configuration>
<property>
<name>fs.defaultFS</name>
<value>hdfs://%HOSTNAME%:8020</value>
</property>
  <property>
 <name>hadoop.security.authentication</name>
<value>kerberos</value>
 </property>
  <property>
 <name>hadoop.security.authorization</name>
<value>true</value>
 </property>
  <!-- HTTPFS proxy user setting -->
  <property>
  <name>hadoop.proxyuser.httpfs.hosts</name>
<value>*</value>
  </property>
<property>
<name>hadoop.proxyuser.httpfs.groups</name>
  <value>*</value>
</property>
  <property>
<name>hadoop.proxyuser.oozie.hosts</name>
<value>*</value>
  </property>
<property>
  <name>hadoop.proxyuser.oozie.groups</name>
  <value>*</value>
</property>
</configuration>