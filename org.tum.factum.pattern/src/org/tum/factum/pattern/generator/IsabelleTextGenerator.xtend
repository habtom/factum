package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.Pattern

class IsabelleTextGenerator {
	
	def static toText(Pattern root) '''
	theory  «root.name»«"\n"»
	imports DynamicArchitectureCalculus«"\n"»
	begin«"\n"»
	
	locale «root.psname» = «FOR ctyp : root.componentTypes»«"\n"»«"\t"»«ctyp.name»: dynamic_component «ctyp.ctsname»cmp «ctyp.ctsname»act «ENDFOR»+«"\n"»
	
	«"\t"»for «FOR ctyp : root.componentTypes»
	«IF ctyp == 0» X «ELSE»
	«"\t"»«"\t"»and  «ctyp.ctsname»act :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"
	«"\t"»«"\t"»and  «ctyp.ctsname»cmp :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> '«ctyp.ctsname»"
	«ENDIF»
	«ENDFOR» + «"\n"»
	
«««	«"\t"»fixes «FOR a : Auxiliary.getInputPorts(root)»
«««	«FOR ctyp : root.componentTypes»«"\t"»«"\t"»and «ctyp.ctsname»«inptport2Text(a)» :: '«ctyp.ctsname» \<Rightarrow>  «inptport2Text2(a)» set«"\n"»«ENDFOR»
«««	«ENDFOR»«FOR a : Auxiliary.getOutputPorts(root) »«FOR ctyp : root.componentTypes»«"\t"»«"\t"»and «ctyp.ctsname»«outptport2Text(a)» :: '«ctyp.ctsname» \<Rightarrow>  «outptport2Text2(a)»«ENDFOR»
«««	«ENDFOR»
	
	begin «"\n"»
	
	...«"\n"»
	
	end
	'''
	//def static dispatch firstElement(ComponentType ct)'''«IF for (element : iterable) {Iterable.getFirst}»'''
	def static dispatch inptport2Text(InputPort inputports)'''«inputports.name»'''
	def static dispatch inptport2Text2(InputPort inptdt)'''«inptdt.sort.name»'''
	def static dispatch outptport2Text(OutputPort outprts)'''«outprts.name»'''
	def static dispatch outptport2Text2(OutputPort outptdt)'''«outptdt.sort.name»
	'''



	def static testX(Pattern root) {
		root.componentTypes.forEach[ element, index | if (index == 0) {
			println(element.ctsname)
		}]
		 
	}
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
 