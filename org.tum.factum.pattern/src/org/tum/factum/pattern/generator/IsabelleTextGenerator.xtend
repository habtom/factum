package org.tum.factum.pattern.generator
///*

import org.eclipse.xtext.EcoreUtil2
import org.tum.factum.pattern.pattern.ActBaseTerms
import org.tum.factum.pattern.pattern.ActBinaryFormulas
import org.tum.factum.pattern.pattern.ActBinaryOperator
import org.tum.factum.pattern.pattern.ActComponentVariable
import org.tum.factum.pattern.pattern.ActFormula
import org.tum.factum.pattern.pattern.ActFormulaWithBracket
import org.tum.factum.pattern.pattern.ActPredicateCAct
import org.tum.factum.pattern.pattern.ActPredicateConn
import org.tum.factum.pattern.pattern.ActPredicateEq
import org.tum.factum.pattern.pattern.ActPredicatePAct
import org.tum.factum.pattern.pattern.ActPredicateTerms
import org.tum.factum.pattern.pattern.ActPredicateVal
import org.tum.factum.pattern.pattern.ActQuantifiedFormulas
import org.tum.factum.pattern.pattern.ActUnaryFormulas
import org.tum.factum.pattern.pattern.AgBaseTerms
import org.tum.factum.pattern.pattern.AgBinaryFormulas
import org.tum.factum.pattern.pattern.AgFormula
import org.tum.factum.pattern.pattern.AgFormulaWithBracket
import org.tum.factum.pattern.pattern.AgPredicateCAct
import org.tum.factum.pattern.pattern.AgPredicateConn
import org.tum.factum.pattern.pattern.AgPredicateEq
import org.tum.factum.pattern.pattern.AgPredicatePAct
import org.tum.factum.pattern.pattern.AgPredicateTerms
import org.tum.factum.pattern.pattern.AgPredicateVal
import org.tum.factum.pattern.pattern.AgQuantifiedFormulas
import org.tum.factum.pattern.pattern.AgUnaryFormulas
import org.tum.factum.pattern.pattern.BinaryOperator
import org.tum.factum.pattern.pattern.ComponentType
import org.tum.factum.pattern.pattern.ComponentVariable
import org.tum.factum.pattern.pattern.CtaBaseTerms
import org.tum.factum.pattern.pattern.CtaBinaryFormulas
import org.tum.factum.pattern.pattern.CtaFormula
import org.tum.factum.pattern.pattern.CtaFormulaWithBracket
import org.tum.factum.pattern.pattern.CtaPredicateCAct
import org.tum.factum.pattern.pattern.CtaPredicateConn
import org.tum.factum.pattern.pattern.CtaPredicateEq
import org.tum.factum.pattern.pattern.CtaPredicatePAct
import org.tum.factum.pattern.pattern.CtaPredicateTerms
import org.tum.factum.pattern.pattern.CtaPredicateVal
import org.tum.factum.pattern.pattern.CtaQuantifiedFormulas
import org.tum.factum.pattern.pattern.CtaUnaryFormulas
import org.tum.factum.pattern.pattern.ImplicitComponentVariable
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.NegUnaryOperator
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.SndImplicitComponentVariable
import org.tum.factum.pattern.pattern.UnaryOperator

class IsabelleTextGenerator {

	def static toIsabelle(Pattern root) '''
	theory «root.name»«"\n"»
	imports DynamicArchitectures.Dynamic_Architecture_Calculus«"\n"»
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
«««	«FOR ctp: root.componentTypes.drop(1)»
	«FOR ctp: root.componentTypes.get(1).parameters»
	«val ctpName = root.componentTypes.get(1).ctsname»
	«val ctParam = ctp.name»
«««	«val ctParam = ctp.parameters.map[name].toString.replaceAll("[\\[\\],]","")»
«««	«IF ctp.parameters !== null»
	«"\t"»«ctpName»«»«ctParam»_unique: "\<And> «ctpName»1  «ctpName»2. \<lbrakk> «ctpName»«ctParam» «ctpName»1 = «ctpName»«ctParam» «ctpName»2\<rbrakk> \<Longrightarrow> «ctpName»1 = «ctpName»2" and«"\n"»
	«"\t"»«ctpName»«»«ctParam»_ex: "\<And>«ctpName»«»«ctParam»'. \<exists>«ctpName». «ctpName»«»«ctParam» «ctpName» = «ctpName»«ctParam»'" and«"\n"»
«««	«ctpName»id_ex: "\<And>sid. \<exists>«ctpName». «ctpName»«ctParam» «ctpName» = sid"
	«ENDFOR»
	«««	Activation formulas
		«FOR ct : root.componentTypes» 
			«IF ct.activation !== null»
				«IF ct.activation.lower !== null»
					«"\t"»act_«ct.ctsname»_lb: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c ((«mapFormula(ct.activation.lower)») \<longrightarrow>\<^sup>c ca (\<lambda>c. «ct.ctsname»active «ct.activation.implCmpVar.name» c))) t 0" and
				«ENDIF»
				«IF ct.activation.upper !== null»
					«"\t"»act_«ct.ctsname»_ub: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. «ct.ctsname»active «ct.activation.implCmpVar.name» c) \<longrightarrow>\<^sup>c («mapFormula(ct.activation.upper)»))) t 0" and
				«ENDIF»
			«ENDIF»
		«ENDFOR»
	«««	End of activation formulas
	«««	Begin of connection
		«FOR ct : root.componentTypes»
			«FOR op: ct.outputPorts»
				«IF op.connection !== null»
					«val sndCTypeShortname = mapActComponentVariableToComponentType(op.connection.implCmpVar2).ctsname»
					«val inputPort = op.connects.name»
					«val sndImplVar = op.connection.implCmpVar2.name»
					«val fstImplVar = op.connection.implCmpVar1.name»
					«IF op.connection.lower !== null»
						«"\t"»conn_«ct.ctsname»_lb: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c ((«mapFormula(op.connection.lower)») \<longrightarrow>\<^sup>c ca (\<lambda>c. «ct.ctsname»«op.name» («ct.ctsname»cmp «fstImplVar» c) \<in> «sndCTypeShortname»«inputPort» («sndCTypeShortname»cmp «sndImplVar» c))) t 0" and
					«ENDIF»
					«IF op.connection.upper !== null»
						«"\t"»conn_«ct.ctsname»_ub: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> (\<box>\<^sub>c (ca (\<lambda>c. «ct.ctsname»«op.name» («ct.ctsname»cmp «fstImplVar» c) \<in> «sndCTypeShortname»«inputPort» («sndCTypeShortname»cmp «sndImplVar» c)) \<longrightarrow>\<^sup>c («mapFormula(op.connection.upper)»))) t 0" and
					«ENDIF»
				«ENDIF»
			«ENDFOR»
		«ENDFOR»
	«««	End of connection
«««	«ENDIF»
«««	«ENDFOR»«"\t"»
«««	«FOR p: root.componentTypes.map[parameters]»
«««	«shortNameFirstCmp»id_ex: "\<And>sid. \<exists>«shortNameFirstCmp». «shortNameFirstCmp»«p.map[name].toString.replaceAll("[\\[\\],]","")» «shortNameFirstCmp» = sid"
«««	«ENDFOR»
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
	«"\t"»conn_«shortNameFirstCmp»«nameOutgoingPort»_«shortNameSecondCmp»«nameConnctingPort»: "\<And> k «cVarOftheoutputPrt» «cVarOftheInputPrt» . \<lbrakk>«shortNameFirstCmp»active «cVarOftheInputPrt» k; «shortNameSecondCmp»active «cVarOftheoutputPrt» k\<rbrakk> \<Longrightarrow> «shortNameFirstCmp»«nameOutgoingPort» («shortNameFirstCmp»cmp «cVarOftheInputPrt» k) \<in> «shortNameSecondCmp»«nameConnctingPort» («shortNameSecondCmp»cmp «cVarOftheoutputPrt» k)" and«"\n"»  
	
««« assumption begins	
	«FOR cta : root.ctaFormulaIds»«"\t"»«cta.name»: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> «val ctaElement = root.ctaFormulaIds.filter[v|v.name == cta.name]»«FOR uf : ctaElement»«mapFormula(uf.ctaFormula)» t 0"«ENDFOR»«IF root.ctaFormulaIds.last() !== cta» and «"\n"»«ENDIF»«ENDFOR»
	
	begin «"\n"»
	«FOR ag : root.agFormulaIds»
	theorem «ag.name»:
	  fixes t
	  assumes "t \<in> arch"
	  shows
	  «"\t"»"«val agElement = root.agFormulaIds.filter[v|v.name == ag.name]»«FOR uf : agElement»«mapFormula(uf.agFormula)»t 0"«ENDFOR»«IF root.ctaFormulaIds.last() !== ag» sorry «"\n"»«ENDIF»
	«ENDFOR»
	
«««	«ENDFOR»
	
«««	...«"\n"»
	end

	'''
	def dispatch static generateBinary(BinaryOperator binaryOp){
		return '''«IF binaryOp.LImplies == '⇒'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LAnd == '∧'»\<and>\<^sup>c «ENDIF»«IF binaryOp.LDisjunct == '∨'»\<or>\<^sup>c «ENDIF»«IF binaryOp.LDoubleImplies == '⇔'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LWeakUntil == 'W'»\<WW>\<^sub>c «ENDIF»«IF binaryOp.LUntil == 'U'»\<UU>\<^sup>c «ENDIF»'''
	}
	def dispatch static generateUnary(UnaryOperator opvalue){
		return '''«IF opvalue.ltlG == 'G'»\<box>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'F'»\<diamond>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'X'»\<circle>\<^sub>c «ENDIF»'''
	}

//CTA Dispatches
	def static Object mapFormula(CtaFormula cf){
		return '''«IF cf instanceof CtaBinaryFormulas»«generateFormula(cf as CtaBinaryFormulas)»«ELSE»«IF cf.ctaBaseTerms !== null»«generateCtaBaseTerms(cf.ctaBaseTerms)»«ENDIF»«IF cf.ctaUnaryFormulas !== null»«generateFormula(cf.ctaUnaryFormulas)»«ENDIF»«IF cf.ctaQuantifiedFormulas !== null»«generateFormula(cf.ctaQuantifiedFormulas)»«ENDIF»«IF cf.ctaBinaryFormulas !== null»«generateFormula(cf.ctaBinaryFormulas as CtaBinaryFormulas)»«ENDIF»«IF cf.ctaFormulaWithBracket !== null»«generateFormula(cf.ctaFormulaWithBracket)»«ENDIF»«ENDIF»'''
	}
	def static generateCtaBaseTerms(CtaBaseTerms baseTerms){
		return '''«IF baseTerms.ctaPredicateCAct !== null»«generateFormula(baseTerms.ctaPredicateCAct)»«ENDIF»«IF baseTerms.ctaPredicatePAct !== null»«generateFormula(baseTerms.ctaPredicatePAct)»«ENDIF»«IF baseTerms.ctaPredicateTerms !== null»«generateFormula(baseTerms.ctaPredicateTerms)»«ENDIF»«IF baseTerms.ctaPredicateConn !== null»«generateFormula(baseTerms.ctaPredicateConn)»«ENDIF»«IF baseTerms.ctaPredicateVal !== null»«generateFormula(baseTerms.ctaPredicateVal)»«ENDIF»«IF baseTerms.ctaPredicateEq !== null»«generateFormula(baseTerms.ctaPredicateEq)»«ENDIF»'''
	}
	def dispatch static generateFormula(CtaBinaryFormulas ctabf){
		return '''«IF ctabf.binaryOperator !== null»«mapFormula(ctabf.left)» «generateBinary(ctabf.binaryOperator)» «mapFormula(ctabf.right)»«ENDIF»«IF ctabf.ctaPrimary !== null»«mapFormula(ctabf.ctaPrimary)»«ENDIF»'''
	}
	def dispatch static generateFormula(CtaQuantifiedFormulas ctaq){
		'''«IF ctaq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «ctaq.quantifierOperator.quantifiedExistsVar.name». «ENDIF»«IF ctaq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «ctaq.quantifierOperator.quantifiedAllVar.name». «ENDIF»«mapFormula(ctaq.ctaQuantifiedFs)»'''
	}
	def dispatch static generateFormula(CtaFormulaWithBracket fwb){
		return '''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.ctaPrimaryFormula)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}
	def dispatch static generateFormula(CtaUnaryFormulas ctau){
		'''«IF ctau.unaryOperator !== null»«generateUnary(ctau.unaryOperator)»«ENDIF»«IF ctau.ctaFormulaLtl !== null»«mapFormula(ctau.ctaFormulaLtl)»«ENDIF»«IF ctau.ctaBaseTerms !== null»«generateCtaBaseTerms(ctau.ctaBaseTerms)»«ENDIF»'''
	}
	def dispatch static generateFormula(CtaPredicateTerms ctat){
		val ctpTerm2Op = ctat.ctaPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.cmptypAssigned.ctsname].toString.replaceAll("[\\[\\],]","")
		//val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpVar = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm1CmpVarRef = ctat.ctaPTerm1.dtTypeVars.name
		'''ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»)'''   //needs refactoring in the next release
	}
	
	def dispatch static generateFormula(CtaPredicateCAct ctapc){
		'''«IF ctapc.CAct == 'cAct'»ca (\<lambda>c. «ctapc.CActCmpVar.cmptypAssigned.ctsname»active «ctapc.CActCmpVar.name» c)«ENDIF»'''		
	}
	def dispatch static generateFormula(CtaPredicatePAct ctapp){
		'''«IF ctapp.PAct== 'pAct'»ca (\<lambda>c. «ctapp.PActCtaCmpVaref.cmpRef.cmptypAssigned.ctsname»active «ctapp.PActCtaCmpVaref.cmpRef.name» c)«ENDIF»'''
	}
	def dispatch static generateFormula(CtaPredicateConn ctaconn){
		val connCmpTypShortName1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpVarInputPort = ctaconn.ctaConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = ctaconn.ctaConnCmpVarOutputPort.outputPrtrf.name
		val connCmpVar1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.name
		'''«IF ctaconn.ctaConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) \<in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c))«ENDIF»'''
	}
	def dispatch static generateFormula(CtaPredicateVal ctapval){
		val valCmpTypShortName = ctapval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valCmpVarFirstInpt = ctapval.valCmpVariableRef.cmpRef.name
		val valCmpPortRef = ctapval.valCmpVariableRef.portRef
				
		if (ctapval.valCmpVariableRef !== null && ctapval.ctaValTerms !== null) {
			switch  valCmpPortRef {
	        InputPort : {
	        	val valCmpVarInputPort = ctapval.valCmpVariableRef.portRef as InputPort
				'''«IF ctapval.ctaVal == 'val' && ctapval.ctaValTerms.termOperatorFunction !== null && valCmpVarInputPort !== null && ctapval.ctaValTerms.termOperatorFunction.trmOperator !== null»«val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»«val valTermCmpTypShortNameSecondInpt = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valTermCmpVarSecondInpt = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.name»ca (\<lambda>c. («valOps» («valTermCmpTypShortNameSecondInpt»«valCmpParm» («valTermCmpTypShortNameSecondInpt»cmp «valTermCmpVarSecondInpt» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))
				«ELSEIF ctapval.ctaVal == 'val' && valCmpVarInputPort !== null && ctapval.ctaValTerms.cmpVariableRef !== null && ctapval.ctaValTerms.cmpVariableRef.cmpRef !== null »«val valCmpPortSecondInpt = ctapval.ctaValTerms.cmpVariableRef.portRef.name»«val valCmpTypShortNameSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
	        }
	        OutputPort : {
	        	val valCmpVarOutputPort = ctapval.valCmpVariableRef.portRef as OutputPort
				'''«IF ctapval.ctaVal == 'val' && ctapval.ctaValTerms !== null»«val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)) «valOpsDtVar» = «valCmpTypShortName»«valCmpVarOutputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))«ENDIF»'''
	        }
	        }
		}
	 }    
	def dispatch static generateFormula(CtaPredicateEq ctapeq){
		'''ca (\<lambda>c. «ctapeq.ctaComponentVariable1.name» = «ctapeq.ctaComponentVariable2.name» )'''
	}
//End of CTA Dispatches

//AG dispatches
	def static Object mapFormula(AgFormula af){
		return '''
			«IF af instanceof AgBinaryFormulas»«generateFormula(af as AgBinaryFormulas)»
			«ELSE»
			«IF af.agBaseTerms !== null»
				«generateAgBaseTerms(af.agBaseTerms)»«ENDIF»«IF af.agUnaryFormulas !== null»«generateFormula(af.agUnaryFormulas)»«ENDIF»«IF af.agQuantifiedFormulas !== null»«generateFormula(af.agQuantifiedFormulas)»«ENDIF»«IF af.agBinaryFormulas !== null»«generateFormula(af.agBinaryFormulas as AgBinaryFormulas)»«ENDIF»«IF af.agFormulaWithBracket !== null»«generateFormula(af.agFormulaWithBracket)»«ENDIF»«ENDIF»'''
	}
	def static generateAgBaseTerms(AgBaseTerms baseTerms){
		return '''«IF baseTerms.agPredicateCAct !== null»«generateFormula(baseTerms.agPredicateCAct)»«ENDIF»«IF baseTerms.agPredicatePAct !== null»«generateFormula(baseTerms.agPredicatePAct)»«ENDIF»«IF baseTerms.agPredicateTerms !== null»«generateFormula(baseTerms.agPredicateTerms)»«ENDIF»«IF baseTerms.agPredicateConn !== null»«generateFormula(baseTerms.agPredicateConn)»«ENDIF»«IF baseTerms.agPredicateVal !== null»«generateFormula(baseTerms.agPredicateVal)»«ENDIF»«IF baseTerms.agPredicateEq !== null»«generateFormula(baseTerms.agPredicateEq)»«ENDIF»'''
	}
	def dispatch static generateFormula(AgBinaryFormulas agbf){
		return '''«IF agbf.binaryOperator !== null»«mapFormula(agbf.left)» «generateBinary(agbf.binaryOperator)» «mapFormula(agbf.right)»«ENDIF»«IF agbf.agPrimary !== null»«mapFormula(agbf.agPrimary)»«ENDIF»'''
	}
	def dispatch static generateFormula(AgQuantifiedFormulas agq){
		'''«IF agq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «agq.quantifierOperator.quantifiedExistsVar.name». «ENDIF»«IF agq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «agq.quantifierOperator.quantifiedAllVar.name». «ENDIF»«mapFormula(agq.agQuantifiedFs)»'''
	}
	def dispatch static generateFormula(AgFormulaWithBracket fwb){
		return '''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.agPrimaryFormula)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}
	def dispatch static generateFormula(AgUnaryFormulas agu){
		'''«IF agu.unaryOperator !== null»«generateUnary(agu.unaryOperator)»«ENDIF»«IF agu.agFormulaLtl !== null»«mapFormula(agu.agFormulaLtl)»«ENDIF»«IF agu.agBaseTerms !== null»«generateAgBaseTerms(agu.agBaseTerms)»«ENDIF»'''
	}
	def dispatch static generateFormula(AgPredicateTerms agt){
		val ctpTerm2Op = agt.agPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.cmptypAssigned.ctsname].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpTypPrt = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpVar = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm1CmpVarRef = agt.agPTerm1.dtTypeVars.name
		'''ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»)'''   //needs refactoring in the next release
	}
	def dispatch static generateFormula(AgPredicateCAct agpc){
		'''«IF agpc.CAct == 'cAct'»ca (\<lambda>c. «agpc.CActCmpVar.cmptypAssigned.ctsname»active «agpc.CActCmpVar.name» c)«ENDIF»'''		
	}
	def dispatch static generateFormula(AgPredicatePAct agpp){
		'''«IF agpp.PAct== 'pAct'»ca (\<lambda>c. «agpp.PActAgCmpVaref.cmpRef.cmptypAssigned.ctsname»active «agpp.PActAgCmpVaref.cmpRef.name» c)«ENDIF»'''
	}
	def dispatch static generateFormula(AgPredicateConn agconn){
		val connCmpTypShortName1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpVarInputPort = agconn.agConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = agconn.agConnCmpVarOutputPort.outputPrtrf.name
		val connCmpVar1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.name
		'''«IF agconn.agConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) \<in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c))«ENDIF»'''
	}
	def dispatch static generateFormula(AgPredicateVal agpval){
		val valCmpTypShortName = agpval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valCmpVarFirstInpt = agpval.valCmpVariableRef.cmpRef.name //if (valCmpVarPort instanceof InputPort) valCmpVarInputPort = valCmpVarPort as InputPort
		val valCmpPortRef = agpval.valCmpVariableRef.portRef
	
		if (agpval.valCmpVariableRef !== null && agpval.agValTerms !== null) {
			switch  valCmpPortRef {
	        InputPort : {
	        	val valCmpVarInputPort = agpval.valCmpVariableRef.portRef as InputPort
				'''«IF agpval.agVal == 'val' && agpval.agValTerms.termOperatorFunction !== null && valCmpVarInputPort !== null && agpval.agValTerms.termOperatorFunction.trmOperator !== null»«val valOps = agpval.agValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = agpval.agValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»«val valTermCmpTypShortNameSecondInpt = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valTermCmpVarSecondInpt = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.name»ca (\<lambda>c. («valOps» («valTermCmpTypShortNameSecondInpt»«valCmpParm» («valTermCmpTypShortNameSecondInpt»cmp «valTermCmpVarSecondInpt» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))
				«ELSEIF agpval.agVal == 'val' && valCmpVarInputPort !== null && agpval.agValTerms.cmpVariableRef !== null && agpval.agValTerms.cmpVariableRef.cmpRef !== null »«val valCmpPortSecondInpt = agpval.agValTerms.cmpVariableRef.portRef.name»«val valCmpTypShortNameSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
	        }
	        OutputPort : {
	        	val valCmpVarOutputPort = agpval.valCmpVariableRef.portRef as OutputPort
				'''«IF agpval.agVal == 'val' && agpval.agValTerms !== null»«val valOps = agpval.agValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = agpval.agValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)) «valOpsDtVar» = «valCmpTypShortName»«valCmpVarOutputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))«ENDIF»'''
	        }
	        }
		}
	    }
	def dispatch static generateFormula(AgPredicateEq agpeq){
		'''ca (\<lambda>c. «agpeq.agComponentVariable1.name» = «agpeq.agComponentVariable2.name» )'''
	}
//End of AG dispatches

//ActFormula Dispatches
	//	remove W and U from the BinaryOperator for ActFormula
	def dispatch static generateBinary(ActBinaryOperator binaryOp){
		return '''«IF binaryOp.LImplies == '⇒'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LAnd == '∧'»\<and>\<^sup>c «ENDIF»«IF binaryOp.LDisjunct == '∨'»\<or>\<^sup>c «ENDIF»«IF binaryOp.LDoubleImplies == '⇔'»\<longrightarrow>\<^sup>c «ENDIF»'''
	}
	
	//remove the G,X,F from the UnaryOperator	
	def dispatch static generateUnary(NegUnaryOperator opvalue){
		 return '''\<not>\<^sup>c'''
	}
	
	def static Object mapFormula(ActFormula af){
		return '''
			«IF af instanceof ActBinaryFormulas»
				«generateFormula(af as ActBinaryFormulas)»
			«ELSE»
			«IF af.actBaseTerms !== null»
				«generateActBaseTerms(af.actBaseTerms)»
			«ENDIF»
			«IF af.actUnaryFormulas !== null»
				«generateFormula(af.actUnaryFormulas)»
			«ENDIF»
			«IF af.actQuantifiedFormulas !== null»
				«generateFormula(af.actQuantifiedFormulas)»
			«ENDIF»
			«IF af.actBinaryFormulas !== null»
				«generateFormula(af.actBinaryFormulas as ActBinaryFormulas)»
			«ENDIF»
			«IF af.actFormulaWithBracket !== null»
				«generateFormula(af.actFormulaWithBracket)»
			«ENDIF»
			«ENDIF»'''
	}
	
	def static generateActBaseTerms(ActBaseTerms abt) {
		return '''
			«IF abt.actPredicateCAct !== null»
				«generateFormula(abt.actPredicateCAct)»
			«ENDIF»
			«IF abt.actPredicatePAct !== null»
				«generateFormula(abt.actPredicatePAct)»
			«ENDIF»
			«IF abt.actPredicateTerms !== null»
				«generateFormula(abt.actPredicateTerms)»
			«ENDIF»
			«IF abt.actPredicateConn !== null»
				«generateFormula(abt.actPredicateConn)»
			«ENDIF»
			«IF abt.actPredicateVal !== null»
				«generateFormula(abt.actPredicateVal)»
			«ENDIF»
			«IF abt.actPredicateEq !== null»
				«generateFormula(abt.actPredicateEq)»
			«ENDIF»			
		'''
	}
	
	def dispatch static generateFormula(ActBinaryFormulas abf){
		return '''
			«IF abf.actBinaryOperator !== null»
				«mapFormula(abf.left)» «generateBinary(abf.actBinaryOperator)» «mapFormula(abf.right)»
			«ENDIF»
			«IF abf.actPrimary !== null»
				«mapFormula(abf.actPrimary)»
			«ENDIF»
		'''
	}
	
	def dispatch static generateFormula(ActQuantifiedFormulas aqf){
		'''
		«IF aqf.actQuantifierOperator.exists == '∃'»
			\<exists>\<^sub>c «aqf.actQuantifierOperator.actQuantifiedExistsVar.name». «
		»«ENDIF»«
		»«IF aqf.actQuantifierOperator.all == '∀'»
			\<forall>\<^sub>c «aqf.actQuantifierOperator.actQuantifiedAllVar.name». «
		»«ENDIF»«
		»«mapFormula(aqf.actQuantifiedFs)»
		'''
	} 
	
	def dispatch static generateFormula(ActFormulaWithBracket fwb){
		'''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.actPrimaryFormula)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}
	
	def dispatch static generateFormula(ActUnaryFormulas auf){
		'''
		«IF auf.actUnaryOperator !== null»
			«generateUnary(auf.actUnaryOperator)»
		«ENDIF»
		«IF auf.actFormulaLtl !== null»
			«mapFormula(auf.actFormulaLtl)»
		«ENDIF»
		«IF auf.actBaseTerms !== null»
			«generateActBaseTerms(auf.actBaseTerms)»
		«ENDIF»
		'''
	}
	def dispatch static generateFormula(ActPredicateTerms apt){
		val func = apt.actPTerm2.termOperatorFunction
		val term2Op = func.trmOperator.name
		val term2CTypeShortName = func.trmOperands.map[actVariableRef.actcmpRef.mapActComponentVariableToComponentType.ctsname].toString.replaceAll("\\[|\\]", "")
		val term2CTypePort = func.trmOperands.map[actVariableRef.actportRef.name].toString.replaceAll("\\[|\\]", "")
		val term2CmpVar = func.trmOperands.map[actVariableRef.actcmpRef.name].toString.replaceAll("\\[|\\]", "")
		val term1DTypeVar = apt.actPTerm1.dtTypeVars.name
		'''ca (\<lambda>c. «term2Op» («term2CTypeShortName»«term2CTypePort» («term2CTypeShortName»cmp «term2CmpVar» c)) = «term1DTypeVar»)'''
	}
	def dispatch static generateFormula(ActPredicateCAct apc){
		'''ca (\<lambda>c. «apc.CActCmpVar.mapActComponentVariableToComponentType.ctsname»active «apc.CActCmpVar.name» c)'''
	}
	
	def dispatch static generateFormula(ActPredicatePAct app){
		'''ca (\<lambda>c. «app.PActCtaCmpVaref.actcmpRef.mapActComponentVariableToComponentType.ctsname»active «app.PActCtaCmpVaref.actcmpRef.name» c)'''
	}
	def dispatch static generateFormula(ActPredicateConn apc){
		val cTypeShortName1 = apc.actConnCmpVarInptPort.actVarRef.mapActComponentVariableToComponentType.ctsname
		val cTypeShortName2 = apc.actConnCmpVarOutputPort.actVarRef.mapActComponentVariableToComponentType.ctsname
		val inputport = apc.actConnCmpVarInptPort.actInputPortRef.name
		val outputport = apc.actConnCmpVarOutputPort.actOutputPortRef.name
		val var1 = apc.actConnCmpVarInptPort.actVarRef.name
		val var2 = apc.actConnCmpVarOutputPort.actVarRef.name
		'''ca (\<lambda>c. «cTypeShortName2»«outputport» («cTypeShortName2»cmp «var2» c) \<in> «cTypeShortName1»«
			inputport» («cTypeShortName1»cmp «var1» c))'''
	}
	def dispatch static generateFormula(ActPredicateVal apv){
		val cTypeShortName = apv.valCmpVariableRef.actcmpRef.mapActComponentVariableToComponentType.ctsname
		val firstInptCmpVar = apv.valCmpVariableRef.actcmpRef.name
		val cmpPortRef = apv.valCmpVariableRef.actportRef
		
		if (apv.valCmpVariableRef !== null && apv.actValTerms !== null){
			switch cmpPortRef{
				InputPort: {
					if (apv.actValTerms.termOperatorFunction !== null){ //check if actValTerms is instance of TermOperatorFunction
						val valOp = apv.actValTerms.termOperatorFunction.trmOperator.name
						val valDTVar = apv.actValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name
						val valCmpParam = apv.actValTerms.termOperatorFunction.trmOperands.get(0).actVariableRef.actcmpRef.mapActComponentVariableToComponentType.parameters.get(0).name
						val valSndInputCTypeShortName = apv.actValTerms.termOperatorFunction.trmOperands.get(0).actVariableRef.actcmpRef.mapActComponentVariableToComponentType.ctsname
						val valSndInputCmpVar = apv.actValTerms.termOperatorFunction.trmOperands.get(0).actVariableRef.actcmpRef.name
						return '''ca (\<lambda>c. («valOp» («valSndInputCTypeShortName»«valCmpParam» («valSndInputCTypeShortName»cmp «valSndInputCmpVar» c)) «
						valDTVar» \<in> «cTypeShortName»«cmpPortRef.name» («cTypeShortName»cmp «firstInptCmpVar» c)))'''
					}
					if (apv.actValTerms.actVariableRef !== null){ ////check if actValTerms is instance of ActCmpVarRef
						val valSndInputCmpPort = apv.actValTerms.actVariableRef.actportRef.name
						val valSndInputCTypeShortName = apv.actValTerms.actVariableRef.actcmpRef.mapActComponentVariableToComponentType.ctsname
						val valSndInputCmpVar = apv.actValTerms.actVariableRef.actcmpRef.name
						return '''ca (\<lambda>c. «valSndInputCTypeShortName»«valSndInputCmpPort» («valSndInputCTypeShortName»cmp «valSndInputCmpVar» c) \<in> «
							cTypeShortName»«cmpPortRef.name» («cTypeShortName»cmp «firstInptCmpVar» c))'''
					}	
				}
				OutputPort: {
					 val func = apv.actValTerms.termOperatorFunction
					 val valOp = func.trmOperator.name
					 val valDTVar = func.trmOperands.get(1).dtTypeVars.name
					 val valCmpParam = func.trmOperands.get(0).actVariableRef.actcmpRef.mapActComponentVariableToComponentType.parameters.get(0).name
					 '''ca (\<lambda>c. («valOp» («cTypeShortName»«valCmpParam» («cTypeShortName»cmp «firstInptCmpVar» c)) «
					 	valDTVar» = «cTypeShortName»«cmpPortRef.name» («cTypeShortName»cmp «firstInptCmpVar» c)))'''
				}
			}
		}
	}
	def dispatch static generateFormula(ActPredicateEq apeq){
		'''ca (\<lambda>c. «apeq.actComponentVariable1.name» = «apeq.actComponentVariable2.name» )'''
	}
	//Help function to return ComponentType of an ActComponentVariable
	def static mapActComponentVariableToComponentType (ActComponentVariable acv){
		if(acv instanceof ComponentVariable){
			return acv.cmptypAssigned
		}
		if(acv instanceof ImplicitComponentVariable){
			return EcoreUtil2.getContainerOfType(acv, ComponentType)
		}
		if(acv instanceof SndImplicitComponentVariable){
			val outputPort = EcoreUtil2.getContainerOfType(acv, OutputPort)
			val ctype = EcoreUtil2.getContainerOfType(outputPort.connects, ComponentType)
			return ctype
		}
	}
	
//End of ActFormula Dispatches
}

