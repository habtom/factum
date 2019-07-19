theory EncryptedConnection
imports DynamicArchitectures.Dynamic_Architecture_Calculus
begin
				
typedecl INT16
typedecl INT32
	
consts add::"INT16 \<Rightarrow> INT16 \<Rightarrow> INT32"
consts sub::"INT32 \<Rightarrow> INT16 \<Rightarrow> INT16"
consts five::"INT16"
					
locale encConnect = 
	enc: dynamic_component enccmp encactive + 
	dec: dynamic_component deccmp decactive + 
	nd: dynamic_component ndcmp ndactive 	
	for encactive :: "'encid \<Rightarrow> cnf \<Rightarrow> bool"
	and enccmp :: "'encid \<Rightarrow> cnf \<Rightarrow> 'enc"
	and deccmp :: "'decid \<Rightarrow> cnf \<Rightarrow> 'dec"
	and decactive :: "'decid \<Rightarrow> cnf \<Rightarrow> bool"
	and ndcmp :: "'ndid \<Rightarrow> cnf \<Rightarrow> 'nd"
	and ndactive :: "'ndid \<Rightarrow> cnf \<Rightarrow> bool"
 + 
 
	fixes encrcvMsg ::"'enc \<Rightarrow> INT16 set"
	and encsndEnc :: "'enc \<Rightarrow> INT32"
	and decrcvEnc :: "'dec \<Rightarrow> INT32 set"
	and decsndDec :: "'dec \<Rightarrow> INT16"
	and ndrcv :: "'nd \<Rightarrow> INT32 set"
	and ndsnd :: "'nd \<Rightarrow> INT32"
					
assumes
	enc: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> \<box>\<^sub>c (ca (\<lambda>c. encactive enc1 c) \<and>\<^sup>c  (\<forall>\<^sub>c enc2. (ca (\<lambda>c. encactive enc2 c) \<longrightarrow>\<^sup>c  ca (\<lambda>c. enc2 = enc1 )))) t 0" and 
	dec: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> \<box>\<^sub>c (ca (\<lambda>c. decactive dec1 c) \<and>\<^sup>c  (\<forall>\<^sub>c dec2. (ca (\<lambda>c. decactive dec2 c) \<longrightarrow>\<^sup>c  ca (\<lambda>c. dec2 = dec1 )))) t 0" and 
	con: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> \<exists>\<^sub>c nd1. (\<exists>\<^sub>c nd2. (\<box>\<^sub>c (ca (\<lambda>c. ndactive nd1 c) \<and>\<^sup>c  ca (\<lambda>c. ndactive nd2 c) \<and>\<^sup>c  ca (\<lambda>c. encsndEnc (enccmp enc1 c) \<in> ndrcv (ndcmp nd1 c)) \<and>\<^sup>c  ca (\<lambda>c. ndsnd (ndcmp nd1 c) \<in> ndrcv (ndcmp nd2 c)) \<and>\<^sup>c  ca (\<lambda>c. ndsnd (ndcmp nd2 c) \<in> decrcvEnc (deccmp dec1 c))))) t 0"
	and 
	bencc: "\<And>t t' encid msg.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> enc.eval encid t t' 0 (\<box>\<^sub>b(([\<lambda>enc. msg \<in> encrcvMsg(enc)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>enc. encsndEnc(enc) = (add msg five)]\<^sub>b))))" and
	bdecc: "\<And>t t' decid msgDec msgEnc.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> dec.eval decid t t' 0 (\<box>\<^sub>b(([\<lambda>dec. msgDec \<in> decrcvEnc(dec)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>dec. decsndDec(dec) = (sub msgEnc five)]\<^sub>b))))" and
	bndc: "\<And>t t' ndid msg.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> nd.eval ndid t t' 0 (\<box>\<^sub>b(([\<lambda>nd. msg \<in> ndrcv(nd)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>nd. ndsnd(nd) = msg]\<^sub>b))))"
theorem g:
fixes t
assumes "t \<in> arch"
shows
	"\<box>\<^sub>c ( \<longrightarrow>\<^sup>c  (\<diamond>\<^sub>c ()))t 0" sorry 
end
