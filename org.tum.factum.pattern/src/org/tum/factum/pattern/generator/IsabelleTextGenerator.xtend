package org.tum.factum.pattern.generator

///*
import org.tum.factum.pattern.pattern.CtaBaseTerms
import org.tum.factum.pattern.pattern.CtaFormula
import org.tum.factum.pattern.pattern.CtaPredicateCAct
import org.tum.factum.pattern.pattern.CtaPredicateConn
import org.tum.factum.pattern.pattern.CtaPredicateEq
import org.tum.factum.pattern.pattern.CtaPredicatePAct
import org.tum.factum.pattern.pattern.CtaPredicateTerms
import org.tum.factum.pattern.pattern.CtaPredicateVal
import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.UnaryOperator
import org.tum.factum.pattern.pattern.CtaUnaryFormulas
import org.tum.factum.pattern.pattern.CtaQuantifiedFormulas
import org.tum.factum.pattern.pattern.CtaBinaryFormulas
import org.tum.factum.pattern.pattern.BinaryOperator
import org.tum.factum.pattern.pattern.CtaFormulaWithBracket
import org.tum.factum.pattern.pattern.AgPredicateEq
import org.tum.factum.pattern.pattern.AgPredicateVal
import org.tum.factum.pattern.pattern.AgPredicateConn
import org.tum.factum.pattern.pattern.AgPredicatePAct
import org.tum.factum.pattern.pattern.AgPredicateCAct
import org.tum.factum.pattern.pattern.AgPredicateTerms
import org.tum.factum.pattern.pattern.AgBaseTerms
import org.tum.factum.pattern.pattern.AgUnaryFormulas
import org.tum.factum.pattern.pattern.AgFormulaWithBracket
import org.tum.factum.pattern.pattern.AgQuantifiedFormulas
import org.tum.factum.pattern.pattern.AgBinaryFormulas
import org.tum.factum.pattern.pattern.AgFormula
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.BtaLImp
import org.tum.factum.pattern.pattern.BtaLOr
import org.tum.factum.pattern.pattern.BtaLAnd
import org.tum.factum.pattern.pattern.LTLOperators
import org.tum.factum.pattern.pattern.BtaTermEq
import org.tum.factum.pattern.pattern.BtaTerm
import org.tum.factum.pattern.pattern.Neg
import org.tum.factum.pattern.pattern.BtaBaseTerm
import org.tum.factum.pattern.pattern.BtaOperation
import org.eclipse.emf.common.util.EList
import org.tum.factum.pattern.pattern.BtaFormula
import org.tum.factum.pattern.pattern.BtaRef
import org.tum.factum.pattern.pattern.BtaWUntil
import org.tum.factum.pattern.pattern.BtaSUntil
import org.tum.factum.pattern.pattern.QuantifierOperator
import org.tum.factum.pattern.pattern.DataTypeVariable
import org.tum.factum.pattern.pattern.PortRef
import org.tum.factum.pattern.pattern.Parameter

class IsabelleTextGenerator {

	def static toIsabelle(Pattern root) '''
	theory «root.name»«"\n"»
	imports DynamicArchitectures.Dynamic_Architecture_Calculus«"\n"»
	begin«"\n"»
					
«««	dt type declarations
	«val dtOps0=root.dtSpec.get(0).dtOps.get(0)»
	«FOR dtSpec : root.dtSpec»
		«FOR sortEVT : dtSpec.dtSorts»
			typedecl «sortEVT.name»
		«ENDFOR»
			
		«FOR dtOp : dtSpec.dtOps»
			consts «dtOp.name»::"«FOR dti : dtOp.dtInput»«dti.name» \<Rightarrow> «ENDFOR»«dtOp.dtOutput.name»"
		«ENDFOR»
	«ENDFOR»
						
	locale «root.psname» = «FOR ctyp : root.componentTypes»«"\n"»«"\t"»«ctyp.ctsname»: dynamic_component «ctyp.ctsname»cmp «ctyp.ctsname»active«IF root.componentTypes.last() !== ctyp» + «ENDIF»«ENDFOR» «««	«IF root.componentTypes.indexOf(ctyp) !== root.componentTypes.size()-1» + «ENDIF»
	
	«"\t"»for «root.componentTypes.get(0).ctsname»active :: "'«root.componentTypes.get(0).ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"
	«"\t"»and «root.componentTypes.get(0).ctsname»cmp :: "'«root.componentTypes.get(0).ctsname»id \<Rightarrow> cnf \<Rightarrow> '«root.componentTypes.get(0).ctsname»"
 	«FOR ctyp : root.componentTypes.drop(1)»
		«"\t"»and «ctyp.ctsname»cmp :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> '«ctyp.ctsname»"
		«"\t"»and «ctyp.ctsname»active :: "'«ctyp.ctsname»id \<Rightarrow> cnf \<Rightarrow> bool"
	«ENDFOR»
	 + 
	 
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
«««	«val shortNameFirstCmp = root.componentTypes.get(1).ctsname»
«««««« the compomnet type that begins connects
«««	«val shortNameSecondCmp = root.componentTypes.get(0).ctsname»
«««	«val nameOutgoingPort = root.componentTypes.get(1).outputPorts.map[name].toString.replaceAll("[\\[\\],]","")»
«««	«val nameConnctingPort = root.componentTypes.get(0).inputPorts.map[name].toString.replaceAll("[\\[\\],]","")»
«««	«FOR ctp: root.componentTypes.get(1).parameters»
«««	«val ctpName = root.componentTypes.get(1).ctsname»
«««	«val ctParam = ctp.name»
«««	«"\t"»«ctpName»«»«ctParam»_unique: "\<And> «ctpName»1  «ctpName»2. \<lbrakk> «ctpName»«ctParam» «ctpName»1 = «ctpName»«ctParam» «ctpName»2\<rbrakk> \<Longrightarrow> «ctpName»1 = «ctpName»2" and«"\n"»
«««	«"\t"»«ctpName»«»«ctParam»_ex: "\<And>«ctpName»«»«ctParam»'. \<exists>«ctpName». «ctpName»«»«ctParam» «ctpName» = «ctpName»«ctParam»'" and«"\n"»
«««	«ENDFOR»
«««
«««	«val cVarOftheInputPrt= root.ctaCmpVar.get(0).name»
«««	«val cVarOftheoutputPrt= root.ctaCmpVar.get(1).name»
«««	«"\t"»conn_«shortNameFirstCmp»«nameOutgoingPort»_«shortNameSecondCmp»«nameConnctingPort»: "\<And> k «cVarOftheoutputPrt» «cVarOftheInputPrt» . \<lbrakk>«shortNameFirstCmp»active «cVarOftheInputPrt» k; «shortNameSecondCmp»active «cVarOftheoutputPrt» k\<rbrakk> \<Longrightarrow> «shortNameFirstCmp»«nameOutgoingPort» («shortNameFirstCmp»cmp «cVarOftheInputPrt» k) \<in> «shortNameSecondCmp»«nameConnctingPort» («shortNameSecondCmp»cmp «cVarOftheoutputPrt» k)" and«"\n"»  
«««	
««« assumption begins	
	«FOR cta : root.ctaFormulaIds»«"\t"»«cta.name»: "\<And>t. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> «val ctaElement = root.ctaFormulaIds.filter[v|v.name == cta.name]»«FOR uf : ctaElement»«mapFormula(uf.ctaFormula)» t 0"«ENDFOR»«IF root.ctaFormulaIds.last() !== cta» and «"\n"»«ENDIF»«ENDFOR»
«««	begin «"\n"»
	«FOR cType : root.componentTypes»
		«FOR ltlFormula : cType.behaviorTraceAssertion»
			«val sname = cType.ctsname»
			«"\t"»b«sname»«ltlFormula.name»: "\<And>t t' «sname»id.\<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> «sname».eval «sname»id t t' 0 («generateLtlFormula(ltlFormula.btaFormula, sname)»)"
			«IF cType.behaviorTraceAssertion.last() !== ltlFormula»«"\t"» and «"\n"»«ENDIF»
		«ENDFOR»
	«ENDFOR»
	«FOR ag : root.agFormulaIds»
		theorem «ag.name»:
		fixes t
		assumes "t \<in> arch"
		shows
		«"\t"»"«val agElement = root.agFormulaIds.filter[v|v.name == ag.name]»«FOR uf : agElement»«mapFormula(uf.agFormula)»t 0"«ENDFOR»«IF root.ctaFormulaIds.last() !== ag» sorry «"\n"»«ENDIF»
	«ENDFOR»	
	end
	'''

	def static generateBinary(BinaryOperator binaryOp) {
		return '''«IF binaryOp.LImplies == '⇒'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LAnd == '∧'»\<and>\<^sup>c «ENDIF»«IF binaryOp.LDisjunct == '∨'»\<or>\<^sup>c «ENDIF»«IF binaryOp.LDoubleImplies == '⇔'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LWeakUntil == 'W'»\<WW>\<^sub>c «ENDIF»«IF binaryOp.LUntil == 'U'»\<UU>\<^sup>c «ENDIF»'''
	}

	def static generateUnary(UnaryOperator opvalue) {
		return '''«IF opvalue.ltlG == 'G'»\<box>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'F'»\<diamond>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'X'»\<circle>\<^sub>c «ENDIF»'''
	}

//CTA Dispatches
	def static Object mapFormula(CtaFormula cf) {
		return '''«IF cf instanceof CtaBinaryFormulas»«generateFormula(cf as CtaBinaryFormulas)»«ELSE»«IF cf.ctaBaseTerms !== null»«generateCtaBaseTerms(cf.ctaBaseTerms)»«ENDIF»«IF cf.ctaUnaryFormulas !== null»«generateFormula(cf.ctaUnaryFormulas)»«ENDIF»«IF cf.ctaQuantifiedFormulas !== null»«generateFormula(cf.ctaQuantifiedFormulas)»«ENDIF»«IF cf.ctaBinaryFormulas !== null»«generateFormula(cf.ctaBinaryFormulas as CtaBinaryFormulas)»«ENDIF»«IF cf.ctaFormulaWithBracket !== null»«generateFormula(cf.ctaFormulaWithBracket)»«ENDIF»«ENDIF»'''
	}

	def static generateCtaBaseTerms(CtaBaseTerms baseTerms) {
		return '''«IF baseTerms.ctaPredicateCAct !== null»«generateFormula(baseTerms.ctaPredicateCAct)»«ENDIF»«IF baseTerms.ctaPredicatePAct !== null»«generateFormula(baseTerms.ctaPredicatePAct)»«ENDIF»«IF baseTerms.ctaPredicateTerms !== null»«generateFormula(baseTerms.ctaPredicateTerms)»«ENDIF»«IF baseTerms.ctaPredicateConn !== null»«generateFormula(baseTerms.ctaPredicateConn)»«ENDIF»«IF baseTerms.ctaPredicateVal !== null»«generateFormula(baseTerms.ctaPredicateVal)»«ENDIF»«IF baseTerms.ctaPredicateEq !== null»«generateFormula(baseTerms.ctaPredicateEq)»«ENDIF»'''
	}

	def dispatch static generateFormula(CtaBinaryFormulas ctabf) {
		return '''«IF ctabf.binaryOperator !== null»«mapFormula(ctabf.left)» «generateBinary(ctabf.binaryOperator)» «mapFormula(ctabf.right)»«ENDIF»«IF ctabf.ctaPrimary !== null»«mapFormula(ctabf.ctaPrimary)»«ENDIF»'''
	}

	def dispatch static generateFormula(CtaQuantifiedFormulas ctaq) {
		'''«IF ctaq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «ctaq.quantifierOperator.quantifiedExistsVar.name». «ENDIF»«IF ctaq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «ctaq.quantifierOperator.quantifiedAllVar.name». «ENDIF»«mapFormula(ctaq.ctaQuantifiedFs)»'''
	}

	def dispatch static generateFormula(CtaFormulaWithBracket fwb) {
		return '''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.ctaPrimaryFormula)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}

	def dispatch static generateFormula(CtaUnaryFormulas ctau) {
		'''«IF ctau.unaryOperator !== null»«generateUnary(ctau.unaryOperator)»«ENDIF»«IF ctau.ctaFormulaLtl !== null»«mapFormula(ctau.ctaFormulaLtl)»«ENDIF»«IF ctau.ctaBaseTerms !== null»«generateCtaBaseTerms(ctau.ctaBaseTerms)»«ENDIF»'''
	}

	def dispatch static generateFormula(CtaPredicateTerms ctat) {
		val ctpTerm2Op = ctat.ctaPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map [
			cmpVariableRef.cmpRef.cmptypAssigned.ctsname
		].toString.replaceAll("[\\[\\],]", "")
		// val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].toString.replaceAll("[\\[\\],]","")
		val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].
			toString.replaceAll("[\\[\\],]", "")
		val ctpTerm2CmpVar = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.
			replaceAll("[\\[\\],]", "")
		val ctpTerm1CmpVarRef = ctat.ctaPTerm1.dtTypeVars.name
		'''ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»)''' // needs refactoring in the next release
	}

	def dispatch static generateFormula(CtaPredicateCAct ctapc) {
		'''«IF ctapc.CAct == 'cAct'»ca (\<lambda>c. «ctapc.CActCmpVar.cmptypAssigned.ctsname»active «ctapc.CActCmpVar.name» c)«ENDIF»'''
	}

	def dispatch static generateFormula(CtaPredicatePAct ctapp) {
		'''«IF ctapp.PAct== 'pAct'»ca (\<lambda>c. «ctapp.PActCtaCmpVaref.cmpRef.cmptypAssigned.ctsname»active «ctapp.PActCtaCmpVaref.cmpRef.name» c)«ENDIF»'''
	}

	def dispatch static generateFormula(CtaPredicateConn ctaconn) {
		val connCmpTypShortName1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpVarInputPort = ctaconn.ctaConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = ctaconn.ctaConnCmpVarOutputPort.outputPrtrf.name
		val connCmpVar1 = ctaconn.ctaConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = ctaconn.ctaConnCmpVarOutputPort.outptPrtCmpRef.name
		'''«IF ctaconn.ctaConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) \<in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c))«ENDIF»'''
	}

	def dispatch static generateFormula(CtaPredicateVal ctapval) {
		val valCmpTypShortName = ctapval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valCmpVarFirstInpt = ctapval.valCmpVariableRef.cmpRef.name
		val valCmpPortRef = ctapval.valCmpVariableRef.portRef

		if (ctapval.valCmpVariableRef !== null && ctapval.ctaValTerms !== null) {
			switch valCmpPortRef {
				InputPort: {
					val valCmpVarInputPort = ctapval.valCmpVariableRef.portRef as InputPort
					'''«IF ctapval.ctaVal == 'val' && ctapval.ctaValTerms.termOperatorFunction !== null && valCmpVarInputPort !== null && ctapval.ctaValTerms.termOperatorFunction.trmOperator !== null»«val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»«val valTermCmpTypShortNameSecondInpt = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valTermCmpVarSecondInpt = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.name»ca (\<lambda>c. («valOps» («valTermCmpTypShortNameSecondInpt»«valCmpParm» («valTermCmpTypShortNameSecondInpt»cmp «valTermCmpVarSecondInpt» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))
				«ELSEIF ctapval.ctaVal == 'val' && valCmpVarInputPort !== null && ctapval.ctaValTerms.cmpVariableRef !== null && ctapval.ctaValTerms.cmpVariableRef.cmpRef !== null»«val valCmpPortSecondInpt = ctapval.ctaValTerms.cmpVariableRef.portRef.name»«val valCmpTypShortNameSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
				}
				OutputPort: {
					val valCmpVarOutputPort = ctapval.valCmpVariableRef.portRef as OutputPort
					'''«IF ctapval.ctaVal == 'val' && ctapval.ctaValTerms !== null»«val valOps = ctapval.ctaValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = ctapval.ctaValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)) «valOpsDtVar» = «valCmpTypShortName»«valCmpVarOutputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))«ENDIF»'''
				}
			}
		}
	}

	def dispatch static generateFormula(CtaPredicateEq ctapeq) {
		'''ca (\<lambda>c. «ctapeq.ctaComponentVariable1.name» = «ctapeq.ctaComponentVariable2.name» )'''
	}

//End of CTA Dispatches
//AG dispatches
	def static Object mapFormula(AgFormula af) {
		return '''«IF af instanceof AgBinaryFormulas»«generateFormula(af as AgBinaryFormulas)»«ELSE»«IF af.agBaseTerms !== null»«generateAgBaseTerms(af.agBaseTerms)»«ENDIF»«IF af.agUnaryFormulas !== null»«generateFormula(af.agUnaryFormulas)»«ENDIF»«IF af.agQuantifiedFormulas !== null»«generateFormula(af.agQuantifiedFormulas)»«ENDIF»«IF af.agBinaryFormulas !== null»«generateFormula(af.agBinaryFormulas as AgBinaryFormulas)»«ENDIF»«IF af.agFormulaWithBracket !== null»«generateFormula(af.agFormulaWithBracket)»«ENDIF»«ENDIF»'''
	}

	def static generateAgBaseTerms(AgBaseTerms baseTerms) {
		return '''«IF baseTerms.agPredicateCAct !== null»«generateFormula(baseTerms.agPredicateCAct)»«ENDIF»«IF baseTerms.agPredicatePAct !== null»«generateFormula(baseTerms.agPredicatePAct)»«ENDIF»«IF baseTerms.agPredicateTerms !== null»«generateFormula(baseTerms.agPredicateTerms)»«ENDIF»«IF baseTerms.agPredicateConn !== null»«generateFormula(baseTerms.agPredicateConn)»«ENDIF»«IF baseTerms.agPredicateVal !== null»«generateFormula(baseTerms.agPredicateVal)»«ENDIF»«IF baseTerms.agPredicateEq !== null»«generateFormula(baseTerms.agPredicateEq)»«ENDIF»'''
	}

	def dispatch static generateFormula(AgBinaryFormulas agbf) {
		return '''«IF agbf.binaryOperator !== null»«mapFormula(agbf.left)» «generateBinary(agbf.binaryOperator)» «mapFormula(agbf.right)»«ENDIF»«IF agbf.agPrimary !== null»«mapFormula(agbf.agPrimary)»«ENDIF»'''
	}

	def dispatch static generateFormula(AgQuantifiedFormulas agq) {
		'''«IF agq.quantifierOperator.exists == '∃'»\<exists>\<^sub>c «agq.quantifierOperator.quantifiedExistsVar.name». «ENDIF»«IF agq.quantifierOperator.all == '∀'»\<forall>\<^sub>c «agq.quantifierOperator.quantifiedAllVar.name». «ENDIF»«mapFormula(agq.agQuantifiedFs)»'''
	}

	def dispatch static generateFormula(AgFormulaWithBracket fwb) {
		return '''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.agPrimaryFormula)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}

	def dispatch static generateFormula(AgUnaryFormulas agu) {
		'''«IF agu.unaryOperator !== null»«generateUnary(agu.unaryOperator)»«ENDIF»«IF agu.agFormulaLtl !== null»«mapFormula(agu.agFormulaLtl)»«ENDIF»«IF agu.agBaseTerms !== null»«generateAgBaseTerms(agu.agBaseTerms)»«ENDIF»'''
	}

	def dispatch static generateFormula(AgPredicateTerms agt) {
		val ctpTerm2Op = agt.agPTerm2.termOperatorFunction.trmOperator.name
		val ctpTerm2CmpTypSN = agt.agPTerm2.termOperatorFunction.trmOperands.map [
			cmpVariableRef.cmpRef.cmptypAssigned.ctsname
		].toString.replaceAll("[\\[\\],]", "")
		val ctpTerm2CmpTypPrt = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.portRef.name].
			toString.replaceAll("[\\[\\],]", "")
		val ctpTerm2CmpVar = agt.agPTerm2.termOperatorFunction.trmOperands.map[cmpVariableRef.cmpRef.name].toString.
			replaceAll("[\\[\\],]", "")
		val ctpTerm1CmpVarRef = agt.agPTerm1.dtTypeVars.name
		'''ca (\<lambda>c. «ctpTerm2Op» («ctpTerm2CmpTypSN»«ctpTerm2CmpTypPrt»	(«ctpTerm2CmpTypSN»cmp «ctpTerm2CmpVar» c)) = «ctpTerm1CmpVarRef»)''' // needs refactoring in the next release
	}

	def dispatch static generateFormula(AgPredicateCAct agpc) {
		'''«IF agpc.CAct == 'cAct'»ca (\<lambda>c. «agpc.CActCmpVar.cmptypAssigned.ctsname»active «agpc.CActCmpVar.name» c)«ENDIF»'''
	}

	def dispatch static generateFormula(AgPredicatePAct agpp) {
		'''«IF agpp.PAct== 'pAct'»ca (\<lambda>c. «agpp.PActAgCmpVaref.cmpRef.cmptypAssigned.ctsname»active «agpp.PActAgCmpVaref.cmpRef.name» c)«ENDIF»'''
	}

	def dispatch static generateFormula(AgPredicateConn agconn) {
		val connCmpTypShortName1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpTypShortName2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.ctsname
		val connCmpVarInputPort = agconn.agConnCmpVarInptPort.inputPrtrf.name
		val connCmpVarOutputPort = agconn.agConnCmpVarOutputPort.outputPrtrf.name
		val connCmpVar1 = agconn.agConnCmpVarInptPort.inptPrtCmpRef.name
		val connCmpVar2 = agconn.agConnCmpVarOutputPort.outptPrtCmpRef.name
		'''«IF agconn.agConn == 'conn'»ca (\<lambda>c. «connCmpTypShortName2»«connCmpVarOutputPort» («connCmpTypShortName2»cmp «connCmpVar2» c) \<in> «connCmpTypShortName1»«connCmpVarInputPort» («connCmpTypShortName1»cmp «connCmpVar1» c))«ENDIF»'''
	}

	def dispatch static generateFormula(AgPredicateVal agpval) {
		val valCmpTypShortName = agpval.valCmpVariableRef.cmpRef.cmptypAssigned.ctsname
		val valCmpVarFirstInpt = agpval.valCmpVariableRef.cmpRef.name // if (valCmpVarPort instanceof InputPort) valCmpVarInputPort = valCmpVarPort as InputPort
		val valCmpPortRef = agpval.valCmpVariableRef.portRef

		if (agpval.valCmpVariableRef !== null && agpval.agValTerms !== null) {
			switch valCmpPortRef {
				InputPort: {
					val valCmpVarInputPort = agpval.valCmpVariableRef.portRef as InputPort
					'''«IF agpval.agVal == 'val' && agpval.agValTerms.termOperatorFunction !== null && valCmpVarInputPort !== null && agpval.agValTerms.termOperatorFunction.trmOperator !== null»«val valOps = agpval.agValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = agpval.agValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»«val valTermCmpTypShortNameSecondInpt = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valTermCmpVarSecondInpt = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.name»ca (\<lambda>c. («valOps» («valTermCmpTypShortNameSecondInpt»«valCmpParm» («valTermCmpTypShortNameSecondInpt»cmp «valTermCmpVarSecondInpt» c)) «valOpsDtVar» \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))
				«ELSEIF agpval.agVal == 'val' && valCmpVarInputPort !== null && agpval.agValTerms.cmpVariableRef !== null && agpval.agValTerms.cmpVariableRef.cmpRef !== null»«val valCmpPortSecondInpt = agpval.agValTerms.cmpVariableRef.portRef.name»«val valCmpTypShortNameSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
				}
				OutputPort: {
					val valCmpVarOutputPort = agpval.valCmpVariableRef.portRef as OutputPort
					'''«IF agpval.agVal == 'val' && agpval.agValTerms !== null»«val valOps = agpval.agValTerms.termOperatorFunction.trmOperator.name»«val valOpsDtVar = agpval.agValTerms.termOperatorFunction.trmOperands.get(1).dtTypeVars.name»«val valCmpParm = agpval.agValTerms.termOperatorFunction.trmOperands.get(0).cmpVariableRef.cmpRef.cmptypAssigned.parameters.get(0).name»ca (\<lambda>c. («valOps» («valCmpTypShortName»«valCmpParm» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)) «valOpsDtVar» = «valCmpTypShortName»«valCmpVarOutputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c)))«ENDIF»'''
				}
			}
		}
	}

	def dispatch static generateFormula(AgPredicateEq agpeq) {
		'''ca (\<lambda>c. «agpeq.agComponentVariable1.name» = «agpeq.agComponentVariable2.name» )'''
	}

	def static String generateLtlFormula(BtaFormula formula, String shortName) {
		switch formula {
			BtaLImp:
				return "(" + generateLtlFormula(formula.left, shortName) + ") \\<longrightarrow>\\<^sup>b (" +
					generateLtlFormula(formula.right, shortName) + ")"
			BtaLOr:
				return generateLtlFormula(formula.left, shortName) + " \\<or>\\<^sup>b " + generateLtlFormula(formula.right, shortName)
			BtaLAnd:
				return generateLtlFormula(formula.left, shortName) + " \\<and>\\<^sup>b " + generateLtlFormula(formula.right, shortName)
			LTLOperators: 
				return  ltlOperator(formula) + "(" + generateLtlFormula(formula.btaFormula, shortName) + ")"
			BtaWUntil:
				return generateLtlFormula(formula.left, shortName) + " \\<WW>\\<^sub>b " + generateLtlFormula(formula.right, shortName)
			BtaSUntil:
				return generateLtlFormula(formula.left, shortName) + " \\<UU>\\<^sub>b " + generateLtlFormula(formula.right, shortName)
			BtaTerm:
				return btaTerm(formula, shortName)
			Neg:
				return "\\<not>\\<^sup>b(" + generateLtlFormula(formula.btaFormula, shortName) + ")"
			QuantifierOperator: 
				return '''«IF formula.exists === null»\<forall>\<^sub>b«formula.quantifiedAllVar.name»«ELSE»\<exists>\<^sub>b«formula.quantifiedExistsVar.name»«ENDIF». «generateLtlFormula(formula.btaFormula, shortName)»'''
			BtaTermEq: {
				val lhs = convertToBtaRef(formula.left)
				val rhs = convertToBtaRef(formula.right)
				
				if (lhs instanceof InputPort && rhs instanceof DataTypeVariable) {
					return '''[\<lambda>«shortName». «rhs.name» \<in> «shortName»«lhs.name»(«shortName»)]\<^sub>b'''
				}
			    return '''[\<lambda>«shortName». «btaTerm(formula.left, shortName)» = «btaTerm(formula.right, shortName)»]\<^sub>b'''
			}
		}
	}
	
	def static BtaRef convertToBtaRef(BtaTerm term) {
		switch term {
			BtaBaseTerm: return term.btaRef
			default: return null
		}
	}

	def static String btaTerm(BtaTerm term, String shortName) {
		switch term {
			BtaBaseTerm: {
				val ref = term.btaRef
				if (ref instanceof InputPort || ref instanceof OutputPort) {
					return '''«shortName»«term.btaRef.name»(«shortName»)'''
				} else {
					return ref.name
				}
			} 
			BtaOperation: return btaFunction(term.btaTrmOperator.name, term.params.btaOperands, shortName)
		}
	}

	def static String btaFunction(String name, EList<BtaTerm> input, String shortName) {
//		return name + input.stream.map[n | btaTerm(n, shortName)].collect(Collectors.joining(",", "(" , ")"))
		return '''«name»«FOR in : input» «btaTerm(in, shortName)»«ENDFOR»'''
	}
	
	def static String ltlOperator(LTLOperators op) {
		switch op {
			case op.ltlG !== null: return "\\<box>\\<^sub>b"
			case op.ltlX !== null: return "\\<circle>\\<^sub>b"
			case op.ltlF !== null: return "\\<diamond>\\<^sub>b"
		}
	}
	
	def static String getName(PortRef ref) {
		switch ref {
			InputPort: return ref.name
			OutputPort: return ref.name
			Parameter: return ref.name
		}
 	}
 	
 	def static String getName(BtaRef variable) {
		switch variable {
			InputPort: return variable.name
			OutputPort: return variable.name
			Parameter: return variable.name
			DataTypeVariable: return variable.name
		}
	}
}
