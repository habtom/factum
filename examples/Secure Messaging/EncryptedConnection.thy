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
 
	fixes encx ::"'enc \<Rightarrow> INT16 set"
	and enco :: "'enc \<Rightarrow> INT32"
	and decx :: "'dec \<Rightarrow> INT32 set"
	and deco :: "'dec \<Rightarrow> INT16"
	and ndx :: "'nd \<Rightarrow> INT32 set"
	and ndo :: "'nd \<Rightarrow> INT32"
					
assumes
	x: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. encactive enc c) \<and>\<^sup>c  (\<forall>\<^sub>c enc2. (ca (\<lambda>c. encactive enc2 c) \<longrightarrow>\<^sup>c  ca (\<lambda>c. enc2 = enc ))))) t 0" and 
	y: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. decactive dec c) \<and>\<^sup>c  (\<forall>\<^sub>c dec2. (ca (\<lambda>c. decactive dec2 c) \<longrightarrow>\<^sup>c  ca (\<lambda>c. dec2 = dec ))))) t 0" and 
	a: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<exists>\<^sub>c nd. (\<box>\<^sub>c (ca (\<lambda>c. ndactive nd c) \<and>\<^sup>c  ca (\<lambda>c. enco (enccmp enc c) \<in> ndx (ndcmp nd c)) \<and>\<^sup>c  ca (\<lambda>c. ndo (ndcmp nd c) \<in> decx (deccmp dec c))))) t 0" and
	bencx: "\<And>t t' encid i.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> enc.eval encid t t' 0 (\<box>\<^sub>b(([\<lambda>enc. i \<in> encx(enc)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>enc. enco(enc) = add i five]\<^sub>b))))" and
	bdecx: "\<And>t t' decid i.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> dec.eval decid t t' 0 (\<box>\<^sub>b(([\<lambda>dec. i \<in> decx(dec)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>dec. deco(dec) = sub i five]\<^sub>b))))" and
	bndx: "\<And>t t' ndid i.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> nd.eval ndid t t' 0 (\<box>\<^sub>b(([\<lambda>nd. i \<in> ndx(nd)]\<^sub>b) \<longrightarrow>\<^sup>b (\<diamond>\<^sub>b([\<lambda>nd. ndo(nd) = i]\<^sub>b))))"
theorem x:
fixes t                                      
assumes "t \<in> arch"
shows
	"(\<box>\<^sub>c ((ca (\<lambda>c. num16 \<in> encx (enccmp enc c))) \<longrightarrow>\<^sup>c (\<diamond>\<^sub>c (ca (\<lambda>c. num16 = deco (deccmp dec c)))))) t 0"
proof
  show "\<forall>n\<ge>0. (ca (\<lambda>c. num16 \<in> encx (enccmp enc c)) \<longrightarrow>\<^sup>c \<diamond>\<^sub>cca (\<lambda>c. num16 = deco (deccmp dec c))) t n"
  proof
    fix n
    show "0 \<le> n \<longrightarrow>
         (ca (\<lambda>c. num16 \<in> encx (enccmp enc c)) \<longrightarrow>\<^sup>c \<diamond>\<^sub>cca (\<lambda>c. num16 = deco (deccmp dec c))) t n"
    proof
      assume "n\<ge>0"
      show "(ca (\<lambda>c. num16 \<in> encx (enccmp enc c)) \<longrightarrow>\<^sup>c \<diamond>\<^sub>cca (\<lambda>c. num16 = deco (deccmp dec c))) t n"
      proof
        assume a1: "ca (\<lambda>c. num16 \<in> encx (enccmp enc c)) t n"
        show "(\<diamond>\<^sub>cca (\<lambda>c. num16 = deco (deccmp dec c))) t n"
        proof
          show "\<exists>na\<ge>n. ca (\<lambda>c. num16 = deco (deccmp dec c)) t na"
          proof
            from a1 have "num16 \<in> encx (enccmp enc (t n))" by auto
            \<dots>
          qed
        qed
      qed
    qed
  qed
qed
end
