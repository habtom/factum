package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.CtaBinaryFormulas
import org.tum.factum.pattern.pattern.CtaFormula
import org.tum.factum.pattern.pattern.CtaPredicateCAct
import org.tum.factum.pattern.pattern.CtaPredicateConn
import org.tum.factum.pattern.pattern.CtaPredicateEq
import org.tum.factum.pattern.pattern.CtaPredicatePAct
import org.tum.factum.pattern.pattern.CtaPredicateVal
import org.tum.factum.pattern.pattern.CtaQuantifiedFormulas
import org.tum.factum.pattern.pattern.CtaUnaryFormulas
import org.tum.factum.pattern.pattern.Pattern

class IsabelleTextGenerator {

	def static toIsabelle(Pattern root) '''
	theory «root.name»«"\n"»
	imports Auxiliary«"\n"»
	begin«"\n"»
	
«««	dt type declarations
	«val sortEVT=root.dtSpec.get(0).dtSorts.get(0).name»
	«val dtOps0=root.dtSpec.get(0).dtOps.get(0)»
	typedecl «sortEVT»
	«FOR dtdecl0 : root.dtSpec»
	«FOR dts : dtdecl0.dtSorts.drop(2)»
	typedecl «dts.name»
	«ENDFOR»
	«ENDFOR»
	consts «dtOps0.name»::"«FOR dti : dtOps0.dtInput»«dti.name» \<Rightarrow> «ENDFOR»«dtOps0.dtOutput.name»"
	
	«FOR dtdecl1 : root.dtSpec.drop(1)»
	«FOR dts : dtdecl1.dtSorts»
	typedecl «dts.name»
	«ENDFOR»
	«FOR dto : dtdecl1.dtOps»
	consts «dto.name»::"«FOR dti : dto.dtInput»«dti.name» \<Rightarrow> «ENDFOR»«dto.dtOutput.name»"
	«ENDFOR»
	«ENDFOR»
	
	locale «root.psname» = «FOR ctyp : root.componentTypes»«"\n"»«"\t"»«ctyp.ctsname»: dynamic_component «ctyp.ctsname»cmp «ctyp.ctsname»active«IF root.componentTypes.last() !== ctyp» + «ENDIF»«ENDFOR» «««	«IF root.componentTypes.indexOf(ctyp) !== root.componentTypes.size()-1» + «ENDIF»
	
	
	«"\t"»for «root.componentTypes.get(0).ctsname»active :: "'«root.componentTypes.get(0).ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"
	«"\t"»and «root.componentTypes.get(0).ctsname»cmp :: "'«root.componentTypes.get(0).ctsname»id \<Rightarrow> cnf \<Rightarrow> '«root.componentTypes.get(0).ctsname»"
	«FOR ctyp : root.componentTypes.drop(1)»
	«"\t"»and «ctyp.ctsname»cmp :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> '«ctyp.ctsname»"
	«"\t"»and «ctyp.ctsname»active :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"«ENDFOR» + «"\n"»
	
	«val inptPrt0 = root.componentTypes.get(0).inputPorts.get(0)»
	«val inptPrt0SortType = inptPrt0.inputPrtSrtTyp.name»
	«val inptPrt0Name = inptPrt0.name»
	«val inptPrtDrop = root.componentTypes.map[inputPorts].drop(1)»
	«val outputPrtDrop = root.componentTypes.map[outputPorts].drop(1)»

	«"\t"»fixes «root.componentTypes.get(0).ctsname»«inptPrt0Name» ::"'«root.componentTypes.get(0).ctsname» \<Rightarrow> «inptPrt0SortType» set"«"\n"»
	«FOR a : inptPrtDrop»«FOR ctyp : root.componentTypes.drop(1)»
	«"\t"»and «ctyp.ctsname»«a.map[name].toString.replaceAll("[\\[\\],]","")» :: "'«ctyp.ctsname» \<Rightarrow> «a.map[it.inputPrtSrtTyp.name].toString.replaceAll("[\\[\\],]","")» set"«"\n"»
	«ENDFOR»«ENDFOR»
	«FOR b : outputPrtDrop»
	«FOR ctyp : root.componentTypes»«"\t"»and «ctyp.ctsname»«b.map[name].toString.replaceAll("[\\[\\],]","")» :: "'«ctyp.ctsname» \<Rightarrow> «b.map[it.outputPrtSrtTyp.name].toString.replaceAll("[\\[\\],]","")»"
	«ENDFOR»
	«ENDFOR»
	
	«"\t"»assumes
«««	«val shortNameFirstCmp = root.componentTypes.get(1).ctsname»«val shortNameSecondCmp = root.componentTypes.get(0).ctsname»
«««	«val nameOutgoingPort = root.componentTypes.get(1).outputPorts.map[name].toString.replaceAll("[\\[\\],]","")»
«««	«"\t"»conn_«shortNameFirstCmp»«nameOutgoingPort»_«shortNameSecondCmp»: "\<And>sb1 sb2. \<lbrakk>sbid sb1 = sbid sb2\<rbrakk> \<Longrightarrow> sb1 = sb2"
«««	«"\t"»and «FOR p: root.componentTypes.map[parameters]» «shortNameFirstCmp»id_ex: "\<And>sid. \<exists>«shortNameFirstCmp». «shortNameFirstCmp»«p.map[name].toString.replaceAll("[\\[\\],]","")» «shortNameFirstCmp» = sid"«ENDFOR»

««« assumption begins	
	«FOR cta : root.ctaFormulaIds»
	«"\t"»«cta.name»: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> «val ctaElement = root.ctaFormulaIds.filter[v|v.name == cta.name]»
	«FOR uf : ctaElement»«mapFormula(uf.ctaFormula)» t 0"«ENDFOR» «IF root.ctaFormulaIds.last() !== cta» and «ENDIF»
	«ENDFOR»
	
	begin «"\n"»
	
	theorem delivery:
	  fixes t
	  assumes "t \<in> arch"
	  shows 
	
	
	...«"\n"»
	
	end
	'''
	
	def static Object mapFormula(CtaFormula cf){
		return '''
		«IF cf.ctaUnaryFormulas !== null»«generateFormula(cf.ctaUnaryFormulas)»«ENDIF»
		«IF cf.ctaQuantifiedFormulas !== null»«generateFormula(cf.ctaQuantifiedFormulas)»«ENDIF»
		«IF cf.ctaPredicateCAct !== null»«generateFormula(cf.ctaPredicateCAct)»«ENDIF»
		«IF cf.ctaPredicatePAct !== null»«generateFormula(cf.ctaPredicatePAct)»«ENDIF»
		«IF cf.ctaPredicateConn !== null»«generateFormula(cf.ctaPredicateConn)»«ENDIF»
		«IF cf.ctaPredicateVal !== null»«generateFormula(cf.ctaPredicateVal)»«ENDIF»
		«IF cf.ctaPredicateEq !== null»«generateFormula(cf.ctaPredicateEq)»«ENDIF»
		«IF cf.ctaBinaryFormulas !== null»«generateFormula(cf.ctaBinaryFormulas)»«ENDIF»
«««		«IF cf !== null»«generateFormula(cf)»«ENDIF»
		'''
		}
	
	def dispatch static generateFormula(CtaUnaryFormulas ctau)
		'''(\«IF ctau.unaryOperator.ltlG == 'G'»<box>\<^sub>c «ENDIF»«IF ctau.unaryOperator.ltlF == 'F'»<diamond>\<^sub>c «ENDIF»«IF ctau.unaryOperator.ltlF == 'X'»<circle>\<^sub>c «ENDIF»«mapFormula(ctau.ctaFormulaLtl)»'''
	
	def dispatch static generateFormula(CtaQuantifiedFormulas ctaq)
		'''«IF ctaq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «ctaq.quantifierOperator.quantifiedExistsVar».«ENDIF»«IF ctaq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «ctaq.quantifierOperator.quantifiedAllVar.name».«ENDIF»'''
	
//	def dispatch static generateFormula(CtaFormula ctb)
//		'''«IF ctb == '('»(«ENDIF» «IF ctb == ')'»)«ENDIF»'''
	def dispatch static generateFormula(CtaPredicateCAct ctapc)
		'''«IF ctapc.CAct == 'cAct'»ca (\<lambda>c. «ctapc.CActCmpVar.cmptypAssigned.ctsname»active «ctapc.CActCmpVar.name» c)«ENDIF»'''
	
	def dispatch static generateFormula(CtaPredicatePAct ctapp)
		'''«IF ctapp.PAct== 'pAct'»ca (\<lambda>c. «ctapp.PActCtaCmpVaref.cmpRef.cmptypAssigned.ctsname»active «ctapp.PActCtaCmpVaref.cmpRef.name» c)«ENDIF»'''
	
	def dispatch static generateFormula(CtaPredicateConn ctaconn){
		val connCmpTypShortName1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		
		val connCmpVarInputPort = ctaconn.ctaConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = ctaconn.ctaConnCmpVarOutputPort.outputPrtrf.name
		
		val connCmpVar1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.name
		
	'''«IF ctaconn.ctaConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) <\in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c)))«ENDIF»'''
	}
	
	def dispatch static generateFormula(CtaPredicateVal ctapval) {
		//val valCmpVarInputPort = ctape.valCtaCmpVaref.prtrf.inputPort.name //or change this to generic 'prtrf' and let it be spefied by the user
		
		val valCmpTypShortName = ctapval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name
		
		val valCmpVar0 = ctapval.valCmpVariableRef.cmpRef.name
		val valCmpVarInputPort = ctapval.valCmpVariableRef.portRef.name
		val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name
		
		val valCmpVar1 = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.name
		
		val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name //[null, org.tum.factum.pattern.pattern.impl.DataTypeVariableImpl@16bde57e (name: e)]
		
		'''«IF ctapval.ctaVal == 'val' && valCmpVarInputPort !== null»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVar0» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName»cmp «valCmpVar0» c))))«ENDIF»'''
		//'''(\«IF ctapval.ctaVal == 'val'» (ca (\<lambda>c. («valOps» («valOpsInput» = «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName» «valCmpVar» c) «ENDIF»\<^sub>c'''
		}
	def dispatch static generateFormula(CtaPredicateEq ctapeq){
		'''ca (\<lambda>c. «ctapeq.ctaComponentVariable1.name» = «ctapeq.ctaComponentVariable2.name» )'''
	}
	
	def dispatch static generateFormula(CtaBinaryFormulas ctabf){
		return '''
		«FOR idx : 0..ctabf.binaryOperator.length-1»«val value = ctabf.binaryOperator.get(idx)»
		
		«IF value.LImplies !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»
		
		«IF value.LAnd !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<and>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»
		
		«IF value.LDisjunct !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<or>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»
		
		«IF value.LDoubleImplies !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»
		
		«IF value.LWeakUntil !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<WW>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»
		
		«IF value.LUntil !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<UU>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«ENDFOR»'''
	}
}
