package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.Pattern

class IsabelleTextGenerator {
	
	def static toText(Pattern root) '''
	theory  «root.name»«"\n"»
	imports Auxiliary«"\n"»
	begin«"\n"»
	
	locale «root.psname» = «FOR ctyp : root.componentTypes»«"\n"»«"\t"»«ctyp.name»: dynamic_component «ctyp.ctsname»cmp «ctyp.ctsname»act «ENDFOR»+«"\n"»
	
	«"\t"»for «FOR ctyp : root.componentTypes»
	«"\t"»«"\t"»and  «ctyp.ctsname»act :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"
	«"\t"»«"\t"»and  «ctyp.ctsname»cmp :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> '«ctyp.ctsname»"«ENDFOR» + «"\n"»
	
	«"\t"»fixes «FOR a : Auxiliary.getInputPorts(root)»
	«FOR ctyp : root.componentTypes»«"\t"»«"\t"»and «ctyp.ctsname»«a.map[name].toString.replaceAll("[\\[\\],]","")» :: '«ctyp.ctsname» \<Rightarrow>  «a.map[it.inputPrtSrtTyp.name].toString.replaceAll("[\\[\\],]","")» set«"\n"»
	«ENDFOR»
	«ENDFOR»
	«FOR b : Auxiliary.getOutputPorts(root)»
	«FOR ctyp : root.componentTypes»«"\t"»«"\t"»and «ctyp.ctsname»«b.map[name].toString.replaceAll("[\\[\\],]","")» :: '«ctyp.ctsname» \<Rightarrow>  «b.map[it.outputPrtSrtTyp.name].toString.replaceAll("[\\[\\],]","")»
	«ENDFOR»
	«ENDFOR»
	
	begin «"\n"»
	
	...«"\n"»
	
	end
	'''
}





/*
 * 
theory Publisher_Subscriber
imports Singleton
begin

locale publisher_subscriber =
  publisher: singleton pbactive pbcmp +
  subscriber: dynamic_component sbcmp sbactive
    
    for pbactive :: "'pid \<Rightarrow> cnf \<Rightarrow> bool"
    and pbcmp :: "'pid \<Rightarrow> cnf \<Rightarrow> 'PB"
    and sbactive :: "'sid \<Rightarrow> cnf \<Rightarrow> bool"
    and sbcmp :: "'sid \<Rightarrow> cnf \<Rightarrow> 'SB" +
  
  fixes pbIn :: "'PB \<Rightarrow> bool set"
    and pbOut :: "'PB \<Rightarrow> int set"
    and sbIn :: "'SB \<Rightarrow> bool set"
    and sbOut :: "'SB \<Rightarrow> int set"
begin

...

end
  
end
 */
 