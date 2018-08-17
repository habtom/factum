theory PublisherSubscriber
imports DynamicArchitectures.Dynamic_Architecture_Calculus
begin

typedecl EVT
typedecl MSG
consts evt::"MSG \<Rightarrow> EVT"

typedecl SID
typedecl SBS
consts sub::"SID \<Rightarrow> EVT \<Rightarrow> SBS"
consts unsub::"SID \<Rightarrow> EVT \<Rightarrow> SBS"

locale ps = 
	pb: dynamic_component pbcmp pbactive + 
	sb: dynamic_component sbcmp sbactive 	

	for pbactive :: "'pbid \<Rightarrow> cnf \<Rightarrow> bool"
	and pbcmp :: "'pbid \<Rightarrow> cnf \<Rightarrow> 'pb"
	and sbcmp :: "'sbid \<Rightarrow> cnf \<Rightarrow> 'sb"
	and sbactive :: "'sbid \<Rightarrow> cnf \<Rightarrow> bool" + 


	fixes pbpsb ::"'pb \<Rightarrow> SBS set"
	and pbpnt :: "'pb \<Rightarrow> MSG"
	and sbsnt :: "'sb \<Rightarrow> MSG set"
	and sbssb :: "'sb \<Rightarrow> SBS"
	and sbid :: "'sb \<Rightarrow> SID"

assumes
	sbid_unique: "\<And> sb1  sb2. \<lbrakk> sbid sb1 = sbid sb2\<rbrakk> \<Longrightarrow> sb1 = sb2" and
	sbid_ex: "\<And>sbid'. \<exists>sb. sbid sb = sbid'" and

	conn_sbssb_pbpsb: "\<And> k q p . \<lbrakk>sbactive p k; pbactive q k\<rbrakk> \<Longrightarrow> sbssb (sbcmp p k) \<in> pbpsb (pbcmp q k)" and

	act_pb: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c  (\<forall>\<^sub>c q. (ca (\<lambda>c. pbactive q c) \<longrightarrow>\<^sup>c  ca (\<lambda>c. q = p ))))) t 0" and 
	conn_sb: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c  ca (\<lambda>c. (sub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))
   \<longrightarrow>\<^sup>c  ((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c  ca (\<lambda>c. pbactive p c) \<and>\<^sup>c  ca (\<lambda>c. evt (pbpnt	(pbcmp p c)) = e) \<longrightarrow>\<^sup>c  ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c  ca (\<lambda>c. (unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))))) t 0"

begin

(*Beginning of: not generated, needs to be copied!*)
lemma globI[intro!]:
  fixes n'
  assumes "\<And>n. n\<ge>n' \<Longrightarrow> \<gamma> t n"
  shows "(\<box>\<^sub>c(\<gamma>)) t n'" using assms glob_def by simp

lemma wUntil_Glob:
  assumes "(\<gamma>' \<WW>\<^sub>c \<gamma>) t n"
    and "(\<box>\<^sub>c(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>''')) t n"
    and "(\<box>\<^sub>c(\<gamma> \<longrightarrow>\<^sup>c \<gamma>'')) t n"
  shows "(\<gamma>''' \<WW>\<^sub>c \<gamma>'') t n"
proof
  from assms(1) have "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>' t n')" using wUntilE by simp
  thus "(\<exists>n''\<ge>n. \<gamma>'' t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>''' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>''' t n')"
  proof
    assume "\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"
    show "(\<exists>n''\<ge>n. \<gamma>'' t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>''' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>''' t n')"
    proof -
      from \<open>\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')\<close> obtain n'' where "n''\<ge>n" and "\<gamma> t n''" and a1: "\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'" by auto
      moreover from assms(3) \<open>n''\<ge>n\<close> have "\<gamma> t n'' \<longrightarrow> \<gamma>'' t n''" by auto
      ultimately have "\<gamma>'' t n''" by simp
      moreover have "\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>''' t n'"
      proof
        fix n'
        show "n'\<ge>n \<longrightarrow> n'< n'' \<longrightarrow> \<gamma>''' t n'"
        proof (rule HOL.impI[OF HOL.impI])
          assume "n'\<ge>n" and "n'<n''"
          with assms(2) have "(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>''') t n'" using globE by simp
          hence "\<gamma>' t n' \<longrightarrow> \<gamma>''' t n'" using impE by auto
          moreover from a1 \<open>n'\<ge>n\<close> \<open>n'<n''\<close> have "\<gamma>' t n'" by simp
          ultimately show "\<gamma>''' t n'" by simp
        qed
      qed
      ultimately show ?thesis using \<open>n''\<ge>n\<close> by auto
    qed
  next
    assume a1: "\<forall>n'\<ge>n. \<gamma>' t n'"
    have "\<forall>n'\<ge>n. \<gamma>''' t n'"
    proof
      fix n'
      show "n'\<ge>n \<longrightarrow> \<gamma>''' t n'"
      proof
        assume "n'\<ge>n"
        with assms(2) have "(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>''') t n'" by auto
        hence "\<gamma>' t n' \<longrightarrow> \<gamma>''' t n'" by auto
        moreover from a1 \<open>n'\<ge>n\<close> have "\<gamma>' t n'" by simp
        ultimately show "\<gamma>''' t n'" by simp
      qed
    qed
    thus "(\<exists>n''\<ge>n. \<gamma>'' t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>''' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>''' t n')" by simp
  qed
qed

lemma imp_Glob:
  assumes "(\<box>\<^sub>c(\<gamma>'' \<longrightarrow>\<^sup>c \<gamma>)) t n"
      and "(\<box>\<^sub>c(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>''')) t n"
    shows "(\<box>\<^sub>c((\<gamma> \<longrightarrow>\<^sup>c \<gamma>') \<longrightarrow>\<^sup>c (\<gamma>'' \<longrightarrow>\<^sup>c \<gamma>'''))) t n"
proof
  fix na
  assume "n\<le>na"
  show "((\<gamma> \<longrightarrow>\<^sup>c \<gamma>') \<longrightarrow>\<^sup>c (\<gamma>'' \<longrightarrow>\<^sup>c \<gamma>''')) t na"
  proof
    assume "(\<gamma> \<longrightarrow>\<^sup>c \<gamma>') t na"
    hence "\<gamma> t na \<longrightarrow> \<gamma>' t na" by auto
    hence "(\<not> \<gamma> t na) \<or> \<gamma>' t na" by simp
    hence "(\<not> \<gamma>'' t na) \<or> \<gamma>''' t na"
    proof
      assume "\<not> \<gamma> t na"
      moreover from assms(1) have "\<gamma>'' t na \<longrightarrow> \<gamma> t na" using \<open>n\<le>na\<close> by auto
      ultimately have "\<not> \<gamma>'' t na" by simp
      thus ?thesis by simp
    next
      assume "\<gamma>' t na"
      moreover from assms(2) have "\<gamma>' t na \<longrightarrow> \<gamma>''' t na" using \<open>n\<le>na\<close> by auto
      ultimately have "\<gamma>''' t na" by simp
      thus ?thesis by simp
    qed
    hence "\<gamma>'' t na \<longrightarrow> \<gamma>''' t na" by auto
    thus "(\<gamma>'' \<longrightarrow>\<^sup>c \<gamma>''') t na" by simp
  qed
qed
(*End of: not generated, needs to be copied!*)

theorem delivery:
  fixes t
  assumes "t \<in> arch"
  shows
  	"(\<box>\<^sub>c (ca (\<lambda>c. sbactive s c) \<and>\<^sup>c  ca (\<lambda>c. (sub (sbid (sbcmp s c)) e = sbssb (sbcmp s c))) \<longrightarrow>\<^sup>c  ((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c  ca (\<lambda>c. evt (pbpnt	(pbcmp p c)) = e) \<longrightarrow>\<^sup>c  ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c  (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c  ca (\<lambda>c. (unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))
  ))))t 0"
(*Beginning of: not generated, needs to be copied!*)
proof
  fix n::nat assume "0\<le>n"
  show "((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. (sub (sbid (sbcmp s c)) e = sbssb (sbcmp s c))))
  \<longrightarrow>\<^sup>c (((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. (unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))))) t n"
  proof
    assume "(ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. (sub (sbid (sbcmp s c)) e = sbssb (sbcmp s c)))) t n"
    hence "sbactive s (t n) \<and> sub (sbid (sbcmp s (t n))) e = sbssb (sbcmp s (t n))" by auto
    moreover have "(\<box>\<^sub>c(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p))))) t 0" using act_pb[OF assms(1)] by simp
    hence "(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p)))) t n" by auto
    hence "(ca (\<lambda>c. pbactive p c)) t n" by auto
    hence "pbactive p (t n)" by auto
    ultimately have "(ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. (sub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))) t n" using conn_sbssb_pbpsb by auto
    moreover from conn_sb[of t p s e] have "(ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. sub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)) \<longrightarrow>\<^sup>c
         (ca (sbactive s) \<and>\<^sup>c ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c
         ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c))) t n" using globE assms(1) by auto
    ultimately have "(((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c (ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))) t n" by simp
    moreover have "(\<box>\<^sub>c(((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<longrightarrow>\<^sup>c
                       ((ca (\<lambda>c. sbactive s c) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))))) t n"
    proof (rule imp_Glob)
      show "(\<box>\<^sub>c(ca (sbactive s) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e) \<longrightarrow>\<^sup>c ca (sbactive s) \<and>\<^sup>c ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e))) t n"
      proof
        fix na assume "na\<ge>n"
        show "(ca (sbactive s) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e) \<longrightarrow>\<^sup>c ca (sbactive s) \<and>\<^sup>c ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) t na"
        proof
          assume "(ca (sbactive s) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) t na"
          moreover have "(\<box>\<^sub>c(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p))))) t 0" using act_pb[OF assms(1)] by simp
          hence "(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p)))) t na" by auto
          hence "(ca (\<lambda>c. pbactive p c)) t na" by auto
          ultimately show "(ca (sbactive s) \<and>\<^sup>c ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e)) t na" by simp
        qed
      qed
    next
      show "(\<box>\<^sub>c(ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c)) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c)))) t n" by auto
    qed
    moreover have "(\<box>\<^sub>c(ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)) \<longrightarrow>\<^sup>c (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c))))) t n"
    proof
      fix na assume "na\<ge>n"
      show "(ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)) \<longrightarrow>\<^sup>c (ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))) t na"
      proof
        assume "(ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c))) t na"
        moreover have "(\<box>\<^sub>c(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p))))) t 0" using act_pb[OF assms(1)] by simp
        hence "(ca (pbactive p) \<and>\<^sup>c (\<forall>\<^sub>cq. (ca (pbactive q) \<longrightarrow>\<^sup>c ca (\<lambda>c. q = p)))) t na" by auto
        hence "(ca (\<lambda>c. pbactive p c)) t na" by auto
        ultimately show "(ca (\<lambda>c. pbactive p c) \<and>\<^sup>c ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c))) t na" by simp
      qed
    qed
    ultimately show "((ca (sbactive s) \<and>\<^sup>c ca (\<lambda>c. evt (pbpnt (pbcmp p c)) = e) \<longrightarrow>\<^sup>c ca (\<lambda>c. pbpnt (pbcmp p c) \<in> sbsnt (sbcmp s c))) \<WW>\<^sub>c (ca (pbactive p) \<and>\<^sup>c ca (\<lambda>c. unsub (sbid (sbcmp s c)) e \<in> pbpsb (pbcmp p c)))) t n" using wUntil_Glob by simp
  qed
qed
(*End of: not generated, needs to be copied!*)

end
