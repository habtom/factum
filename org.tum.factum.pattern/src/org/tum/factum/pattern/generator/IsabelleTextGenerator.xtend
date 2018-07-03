package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.CtaBinaryFormulas
import org.tum.factum.pattern.pattern.CtaFormula
import org.tum.factum.pattern.pattern.CtaPredicateCAct
import org.tum.factum.pattern.pattern.CtaPredicateConn
import org.tum.factum.pattern.pattern.CtaPredicateEq
import org.tum.factum.pattern.pattern.CtaPredicatePAct
import org.tum.factum.pattern.pattern.CtaPredicateTerms
import org.tum.factum.pattern.pattern.CtaPredicateVal
import org.tum.factum.pattern.pattern.CtaQuantifiedFormulas
import org.tum.factum.pattern.pattern.CtaUnaryFormulas
import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.AgUnaryFormulas
import org.tum.factum.pattern.pattern.AgFormula
//import org.tum.factum.pattern.pattern.AgFormulaIds
import org.tum.factum.pattern.pattern.AgQuantifiedFormulas
import org.tum.factum.pattern.pattern.AgPredicateTerms
import org.tum.factum.pattern.pattern.AgPredicateCAct
import org.tum.factum.pattern.pattern.AgPredicatePAct
import org.tum.factum.pattern.pattern.AgPredicateConn
import org.tum.factum.pattern.pattern.AgPredicateVal
import org.tum.factum.pattern.pattern.AgPredicateEq
import org.tum.factum.pattern.pattern.AgBinaryFormulas

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

«««	Inputports have 'set' at the end and output ports and parameters not 
	«"\t"»fixes «root.componentTypes.get(0).ctsname»«inptPrt0Name» ::"'«root.componentTypes.get(0).ctsname» \<Rightarrow> «inptPrt0SortType» set"«"\n"»
	«FOR ctyp : root.componentTypes.get(0).outputPorts»
	«"\t"»and «root.componentTypes.get(0).ctsname»«ctyp.name» :: "'«root.componentTypes.get(0).ctsname» \<Rightarrow> «ctyp.outputPrtSrtTyp.name»"
	«ENDFOR»
	«FOR ctyp : root.componentTypes.drop(1)»
	«FOR ip : ctyp.inputPorts»
	«"\t"»and «ctyp.ctsname»«ip.name» :: "'«ctyp.ctsname» \<Rightarrow> «ip.inputPrtSrtTyp.name» set"«"\n"»
	«ENDFOR»
	«FOR op : ctyp.outputPorts»
	«"\t"»and «ctyp.ctsname»«op.name» :: "'«ctyp.ctsname» \<Rightarrow> «op.outputPrtSrtTyp.name»"
	«ENDFOR»
	«FOR p : ctyp.parameters»
	«"\t"»and «ctyp.ctsname»«p.name» :: "'«ctyp.ctsname» \<Rightarrow> «p.paramSrtTyp.name»"
	«ENDFOR»
	«ENDFOR»
	
	assumes
	«val shortNameFirstCmp = root.componentTypes.get(1).ctsname»««« the compomnet type that begins connects
	«val shortNameSecondCmp = root.componentTypes.get(0).ctsname»
	«val nameOutgoingPort = root.componentTypes.get(1).outputPorts.map[name].toString.replaceAll("[\\[\\],]","")»
	«val nameConnctingPort = root.componentTypes.get(0).inputPorts.map[name].toString.replaceAll("[\\[\\],]","")»
	«FOR ctp: root.componentTypes.drop(1)»
	«val ctParam = ctp.parameters.map[name].toString.replaceAll("[\\[\\],]","")»
«««	«IF ctp.parameters !== null»
	«"\t"»«ctp.ctsname»«»«ctParam»_unique: "\<And> «ctp.ctsname»1  «ctp.ctsname»2. \<lbrakk> «ctp.ctsname»«ctParam» «ctp.ctsname»1 = «ctp.ctsname»«ctParam» «ctp.ctsname»2\<rbrakk> \<Longrightarrow> «ctp.ctsname»1 = «ctp.ctsname»2" and«"\n"»
	«"\t"»«ctp.ctsname»«»«ctParam»_ex: "\<And>«ctp.ctsname»«»«ctParam». \<exists>«ctp.ctsname». «ctp.ctsname»«»«ctParam» «ctp.ctsname» = «ctp.ctsname»«»«ctParam»" and«"\n"»
«««	«ENDIF»
«««	«ENDFOR»
	«"\t"»«FOR p: root.componentTypes.map[parameters]» «shortNameFirstCmp»id_ex: "\<And>sid. \<exists>«shortNameFirstCmp». «shortNameFirstCmp»«p.map[name].toString.replaceAll("[\\[\\],]","")» «shortNameFirstCmp» = sid"«ENDFOR»
	«««	«FOR ctp: root.componentTypes»
	«««	«val ctParam = ctp.parameters»
	«««	«IF ctParam !== null»
	«««	«ctp.ctsname»id_ex: "\<And>sid. \<exists>«ctp.ctsname». «ctp.ctsname»«ctParam.map[name]» «ctp.ctsname» = sid"
	«««	«ENDIF»
	«««	«ENDFOR»	
««« must be generated from connects 

	«val cVarOftheInputPrt= root.ctaCmpVar.get(0).name»
	«val cVarOftheoutputPrt= root.ctaCmpVar.get(1).name»
«««	«val prtOfSecondVar= root.ctaCmpVar.get(1).cmptypAssigned.outputPorts.get(0).name» 
«««	«val prtOfFirstVar= root.ctaCmpVar.get(0).cmptypAssigned.outputPorts.get(0).name» 
«««	«val cVarOftheInputPrt= root.componentTypes.map[outputPorts.map[connects]]»
«««	«val cVarOftheInputPrt= root.componentTypes.map[outputPorts.filter[connects]].map[name])»
	«"\t"»conn_«shortNameFirstCmp»«nameOutgoingPort»_«shortNameSecondCmp»«nameConnctingPort»: "\<And> k «cVarOftheoutputPrt» «cVarOftheInputPrt»\<lbrakk>«shortNameFirstCmp»active «cVarOftheoutputPrt» k; «shortNameSecondCmp»active «cVarOftheoutputPrt» k\<rbrakk> \<Longrightarrow> «shortNameSecondCmp»«nameConnctingPort» («shortNameSecondCmp»cmp «cVarOftheoutputPrt» k) \<in> «shortNameFirstCmp»«nameOutgoingPort» («shortNameFirstCmp»cmp «cVarOftheInputPrt» k)" and«"\n"»  
	
	
	
««« assumption begins	
	«FOR cta : root.ctaFormulaIds»«"\t"»«cta.name»: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> «val ctaElement = root.ctaFormulaIds.filter[v|v.name == cta.name]»«FOR uf : ctaElement»«mapFormula(uf.ctaFormula)» t 0"«ENDFOR»«IF root.ctaFormulaIds.last() !== cta» and «"\n"»«ENDIF»«ENDFOR»
	
	begin «"\n"»
	
	theorem delivery:
	  fixes t
	  assumes "t \<in> arch"
	  shows 
	
	«FOR ag : root.agFormulaIds»
	«"\t"»"«val agElement = root.agFormulaIds.filter[v|v.name == ag.name]»
	«FOR uf : agElement»«mapFormula(uf.agFormula)»t 0"
	«ENDFOR»
	«IF root.ctaFormulaIds.last() !== ag» and «"\n"»«ENDIF»
	«ENDFOR»
	«ENDFOR»
	
	
	...«"\n"»
	
	end
	'''
	//CTA Dispatches
	def static Object mapFormula(CtaFormula cf){
		return '''«IF cf.ctaUnaryFormulas !== null»«generateFormula(cf.ctaUnaryFormulas)»«ENDIF»«IF cf.ctaQuantifiedFormulas !== null»«generateFormula(cf.ctaQuantifiedFormulas)»«ENDIF»«IF cf.ctaPredicateCAct !== null»«generateFormula(cf.ctaPredicateCAct)»«ENDIF»«IF cf.ctaPredicatePAct !== null»«generateFormula(cf.ctaPredicatePAct)»«ENDIF»«IF cf.ctaPredicateTerms !== null»«generateFormula(cf.ctaPredicateTerms)»«ENDIF»«IF cf.ctaPredicateConn !== null»«generateFormula(cf.ctaPredicateConn)»«ENDIF»«IF cf.ctaPredicateVal !== null»«generateFormula(cf.ctaPredicateVal)»«ENDIF»«IF cf.ctaPredicateEq !== null»«generateFormula(cf.ctaPredicateEq)»«ENDIF»«IF cf.ctaBinaryFormulas !== null»«generateFormula(cf.ctaBinaryFormulas)»«ENDIF»'''
	}
	def dispatch static generateFormula(CtaUnaryFormulas ctau)
		'''(\«IF ctau.unaryOperator.ltlG == 'G'»<box>\<^sub>c «ENDIF»«IF ctau.unaryOperator.ltlF == 'F'»<diamond>\<^sub>c «ENDIF»«IF ctau.unaryOperator.ltlF == 'X'»<circle>\<^sub>c «ENDIF»«mapFormula(ctau.ctaFormulaLtl)»'''
	def dispatch static generateFormula(CtaQuantifiedFormulas ctaq)
		'''«IF ctaq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «ctaq.quantifierOperator.quantifiedExistsVar.name».«ENDIF»«IF ctaq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «ctaq.quantifierOperator.quantifiedAllVar.name».«ENDIF»«mapFormula(ctaq.ctaQuantifiedFs)»'''
	def dispatch static generateFormula(CtaPredicateTerms ctat) {
		val ctpTerm2Op = ctat.ctaPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.cmptypAssigned.ctsname].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpVar = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm1CmpVarRef = ctat.ctaPTerm1.dtTypeVars.name
		'''(ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»))'''   //needs refactoring in the next release
	}
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
		val valCmpTypShortName = ctapval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name
		val valCmpVar0 = ctapval.valCmpVariableRef.cmpRef.name
		val valCmpVarInputPort = ctapval.valCmpVariableRef.portRef.name
		val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name
		val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name //[null, org.tum.factum.pattern.pattern.impl.DataTypeVariableImpl@16bde57e (name: e)]
		'''«IF ctapval.ctaVal == 'val' && valCmpVarInputPort !== null»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVar0» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName»cmp «valCmpVar0» c))))«ENDIF»'''
		//'''(\«IF ctapval.ctaVal == 'val'» (ca (\<lambda>c. («valOps» («valOpsInput» = «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName» «valCmpVar» c) «ENDIF»\<^sub>c'''
		}
	def dispatch static generateFormula(CtaPredicateEq ctapeq){
		'''ca (\<lambda>c. «ctapeq.ctaComponentVariable1.name» = «ctapeq.ctaComponentVariable2.name» )'''
	}
	def dispatch static generateFormula(CtaBinaryFormulas ctabf){
		return '''«FOR idx : 0..ctabf.binaryOperator.length-1»«val value = ctabf.binaryOperator.get(idx)»«IF value.LImplies !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«IF value.LAnd !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<and>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«IF value.LDisjunct !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<or>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«IF value.LDoubleImplies !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«IF value.LWeakUntil !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<WW>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«IF value.LUntil !== null»«IF idx==0»«mapFormula(ctabf.ctaFormulaLgk.get(idx))»«ENDIF»\<UU>\<^sup>c «mapFormula(ctabf.ctaFormulaLgk.get(idx+1))»«ENDIF»«ENDFOR»'''
	}
	//End of CTA Dispatches
	//AG dispatches
	def static Object mapFormula(AgFormula agcf){
		return '''«IF agcf.agUnaryFormulas !== null»«generateFormula(agcf.agUnaryFormulas)»«ENDIF»«IF agcf.agQuantifiedFormulas !== null»«generateFormula(agcf.agQuantifiedFormulas)»«ENDIF»«IF agcf.agPredicateCAct !== null»«generateFormula(agcf.agPredicateCAct)»«ENDIF»«IF agcf.agPredicatePAct !== null»«generateFormula(agcf.agPredicatePAct)»«ENDIF»«IF agcf.agPredicateTerms !== null»«generateFormula(agcf.agPredicateTerms)»«ENDIF»«IF agcf.agPredicateConn !== null»«generateFormula(agcf.agPredicateConn)»«ENDIF»«IF agcf.agPredicateVal !== null»«generateFormula(agcf.agPredicateVal)»«ENDIF»«IF agcf.agPredicateEq !== null»«generateFormula(agcf.agPredicateEq)»«ENDIF»«IF agcf.agBinaryFormulas !== null»«generateFormula(agcf.agBinaryFormulas)»«ENDIF»'''
		}
	def dispatch static generateFormula(AgUnaryFormulas agu)
		'''(\«IF agu.unaryOperator.ltlG == 'G'»<box>\<^sub>c «ENDIF»«IF agu.unaryOperator.ltlF == 'F'»<diamond>\<^sub>c «ENDIF»«IF agu.unaryOperator.ltlF == 'X'»<circle>\<^sub>c «ENDIF»«mapFormula(agu.agFormulaLtl)»'''
	def dispatch static generateFormula(AgQuantifiedFormulas agq)
		'''«IF agq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «agq.quantifierOperator.quantifiedExistsVar.name».«ENDIF»«IF agq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «agq.quantifierOperator.quantifiedAllVar.name».«ENDIF»«mapFormula(agq.agQuantifiedFs)»'''
	def dispatch static generateFormula(AgPredicateTerms agt) {
		val ctpTerm2Op = agt.agPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.cmptypAssigned.ctsname].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpTypPrt = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpVar = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm1CmpVarRef = agt.agPTerm1.dtTypeVars.name
		'''(ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»))'''   //needs refactoring in the next release
	}
	def dispatch static generateFormula(AgPredicateCAct agpc)
		'''«IF agpc.CAct == 'cAct'»ca (\<lambda>c. «agpc.CActCmpVar.cmptypAssigned.ctsname»active «agpc.CActCmpVar.name» c)«ENDIF»'''
	def dispatch static generateFormula(AgPredicatePAct agpp)
		'''«IF agpp.PAct== 'pAct'»ca (\<lambda>c. «agpp.PActAgCmpVaref.cmpRef.cmptypAssigned.ctsname»active «agpp.PActAgCmpVaref.cmpRef.name» c)«ENDIF»'''
	def dispatch static generateFormula(AgPredicateConn agconn){
		val connCmpTypShortName1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpVarInputPort = agconn.agConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = agconn.agConnCmpVarOutputPort.outputPrtrf.name
		val connCmpVar1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.name
	'''«IF agconn.agConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) <\in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c)))«ENDIF»'''
	}
	def dispatch static generateFormula(AgPredicateVal agpval) {
		val valCmpTypShortName = agpval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valOps = agpval.agValTerms.termOperatorFunction.trmOperator.name
		val valCmpVar0 = agpval.valCmpVariableRef.cmpRef.name
		val valCmpVarInputPort = agpval.valCmpVariableRef.portRef.name
		val valCmpParm = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name
		val valOpsDtVar = agpval.agValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name //[null, org.tum.factum.pattern.pattern.impl.DataTypeVariableImpl@16bde57e (name: e)]
		'''«IF agpval.agVal == 'val' && valCmpVarInputPort !== null»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVar0» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName»cmp «valCmpVar0» c))))«ENDIF»'''
		//'''(\«IF agpval.agVal == 'val'» (ca (\<lambda>c. («valOps» («valOpsInput» = «valCmpTypShortName»«valCmpVarInputPort» («valCmpTypShortName» «valCmpVar» c) «ENDIF»\<^sub>c'''
		}
		
	def dispatch static generateFormula(AgPredicateEq agpeq){
		'''ca (\<lambda>c. «agpeq.agComponentVariable1.name» = «agpeq.agComponentVariable2.name» )'''
	}
	def dispatch static generateFormula(AgBinaryFormulas agbf){
		return '''«FOR idx : 0..agbf.binaryOperator.length-1»«val value = agbf.binaryOperator.get(idx)»«IF value.LImplies !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«IF value.LAnd !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<and>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«IF value.LDisjunct !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<or>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«IF value.LDoubleImplies !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<longrightarrow>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«IF value.LWeakUntil !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<WW>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«IF value.LUntil !== null»«IF idx==0»«mapFormula(agbf.agFormulaLgk.get(idx))»«ENDIF»\<UU>\<^sup>c «mapFormula(agbf.agFormulaLgk.get(idx+1))»«ENDIF»«ENDFOR»'''
	}
	//end of AG dispatches
}
