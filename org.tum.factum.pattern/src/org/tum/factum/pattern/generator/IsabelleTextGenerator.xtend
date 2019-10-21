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
import org.tum.factum.pattern.pattern.DataTypeSpec
import org.tum.factum.pattern.pattern.ComponentType
import org.tum.factum.pattern.pattern.Contract
import org.tum.factum.pattern.pattern.Connection
import org.eclipse.emf.common.util.EList
import java.util.ArrayList
import org.tum.factum.pattern.pattern.BasicFormula
import org.tum.factum.pattern.pattern.ContractTrigger
import org.tum.factum.pattern.pattern.impl.BasicPredicateImpl
import org.tum.factum.pattern.pattern.impl.BasicLAndImpl
import org.tum.factum.pattern.pattern.impl.BasicLOrImpl
import org.tum.factum.pattern.pattern.BasicPredicate
import org.tum.factum.pattern.pattern.DTPredicate
import org.tum.factum.pattern.pattern.impl.BasicBaseTermImpl
import org.tum.factum.pattern.pattern.impl.DataTypeVariableImpl
import org.tum.factum.pattern.pattern.BasicBaseTerm
import org.tum.factum.pattern.pattern.BasicTerm
import org.tum.factum.pattern.pattern.Operation
import org.tum.factum.pattern.pattern.BasicOperation
import org.tum.factum.pattern.pattern.BasicTermEq
import org.tum.factum.pattern.pattern.ProofContract
import org.tum.factum.pattern.pattern.ProofStepRefWithConnections
import org.tum.factum.pattern.pattern.ProofTermMapping

class IsabelleTextGenerator {

	def static toIsabelle(Pattern root) '''
	theory «root.name»«"\n"»
	imports Main«"\n"»
	begin«"\n"»
	
«««	dt type declarations
	«FOR dtdecl0 : root.dtSpec»
		«FOR dts : dtdecl0.dtSorts»
		typedecl «dtdecl0.name»_«dts.name»
		«ENDFOR»
		«FOR dto : dtdecl0.dtOps»
		consts «getOperationName(dto)»::"«FOR dti : dto.dtInput»«(dti.eContainer as DataTypeSpec).name»_«dti.name» \<Rightarrow> «ENDFOR»«(dto.dtOutput.eContainer as DataTypeSpec).name»_«dto.dtOutput.name»"
		«ENDFOR»
		«FOR dtPredicate : dtdecl0.dtPredicate»
		consts «getPredicateName(dtPredicate)»::"«FOR dti : dtPredicate.PInput»«(dti.eContainer as DataTypeSpec).name»_«dti.name» \<Rightarrow> «ENDFOR»bool"
		«ENDFOR»
	«ENDFOR»

	locale «root.psname» =
	«val inptPrt0 = root.componentTypes.get(0).inputPorts.get(0)»
	«val inptPrt0SortType = inptPrt0.inputPrtSrtTyp.name»
	«val inptPrt0Name = inptPrt0.name»
«««	Inputports have 'set' at the end and output ports and parameters not 
	«"\t"»fixes «root.componentTypes.get(0).name»__«inptPrt0Name» ::"nat \<Rightarrow> «(inptPrt0.inputPrtSrtTyp.eContainer as DataTypeSpec).name»_«inptPrt0SortType»"«"\n"»
	«FOR ctyp : root.componentTypes.get(0).outputPorts»
	«"\t"»and «root.componentTypes.get(0).name»__«ctyp.name» :: "nat \<Rightarrow> «(ctyp.outputPrtSrtTyp.eContainer as DataTypeSpec).name»_«ctyp.outputPrtSrtTyp.name»"
	«ENDFOR»
	«FOR ctyp : root.componentTypes.drop(1)»
	«FOR ip : ctyp.inputPorts»
	«"\t"»and «ctyp.name»__«ip.name» :: "nat \<Rightarrow> «(ip.inputPrtSrtTyp.eContainer as DataTypeSpec).name»_«ip.inputPrtSrtTyp.name»"«"\n"»
	«ENDFOR»
	«FOR op : ctyp.outputPorts»
	«"\t"»and «ctyp.name»__«op.name» :: "nat \<Rightarrow> «(op.outputPrtSrtTyp.eContainer as DataTypeSpec).name»_«op.outputPrtSrtTyp.name»"
	«ENDFOR»
	«FOR p : ctyp.parameters»
	«"\t"»and «ctyp.name»__«p.name» :: "nat \<Rightarrow> «(p.paramSrtTyp.eContainer as DataTypeSpec).name»_«p.paramSrtTyp.name»"
	«ENDFOR»
	«ENDFOR»
	
	assumes
	«generateContractsAndConnections(root.componentTypes, root.connections)»
	«generateProofContracts(root.proofContracts)»
	end
	'''
	def static generateContractsAndConnections(EList<ComponentType> components, EList<Connection> connections) {
		var firstContractEntered = false
		var firstConnectionEntered = false
		var contractsCode = new ArrayList<String>();
		var connectionsCode = new ArrayList<String>();
		
		if (components !== null) {
			for(component: components) {
				if (component.contracts !== null) {
					for (contract: component.contracts) {
						if (firstContractEntered) {
							contractsCode.add('''«"\t"»and «generateContract(contract, component)»«"\n"»''')
						}
						else {
							contractsCode.add('''«"\t"»«generateContract(contract, component)»«"\n"»''')
							firstContractEntered = true;
						}
					}
				}
			}
		}
		
		if (connections !== null) {
			for (connection: connections) {
				if (firstContractEntered || firstConnectionEntered) {
					connectionsCode.add('''«"\t"»and «generateConnection(connection)»«"\n"»''')
				} else {
					connectionsCode.add('''«"\t"»«generateConnection(connection)»«"\n"»''')
					firstConnectionEntered = true;
				}
			}
		}
		
		
		return '''«FOR contractCode : contractsCode»«contractCode»«ENDFOR»«FOR connectionCode : connectionsCode»«connectionCode»«ENDFOR»'''
	}
	
	def static String generateTrigger(ContractTrigger trigger) {
		return generateFormula(trigger.formula, trigger.timepoint, null)
	}
	
	def static String generateGuarantee(BasicFormula formula, String timepoint) {
		return generateFormula(formula, timepoint, null)
	}
	
	def static String generateContract(Contract contract, ComponentType component) {
		return '''«component.name»__«contract.name»: '''
		+ '''"\<And>(n::nat)«FOR dtVar: contract.contractDtVar» («dtVar.name»::«(dtVar.varSortType.eContainer as DataTypeSpec).name»_«dtVar.varSortType.name»)«ENDFOR». '''
		+ '''«IF contract.triggers !== null && contract.triggers.size() > 0»\<lbrakk>«contract.triggers.join("", "; ","", [trigger| generateTrigger(trigger)])»\<rbrakk> \<Longrightarrow> «ENDIF»'''+
		'''«generateGuarantee(contract.guarantee, contract.duration)»"'''
	}
	
	def static String generateConnection(Connection connection) {
		return '''«connection.name»: "\<And>(n::nat). («getInputPortName(connection.inputPort as InputPort)» n = «getOutputPortName(connection.outputPort as OutputPort)» n)"'''
	}
	
	def static String generateFormula(BasicFormula formula, String timepoint, EList<ProofTermMapping> mappings) {
		if (formula instanceof BasicPredicateImpl) {
			return generatePredicate(formula, timepoint, mappings)
		}
		else if (formula instanceof BasicTermEq) {
			return generateBasicTermEq(formula, timepoint, mappings)
		}
		else if (formula instanceof BasicLAndImpl) {
			return generateBasicLAnd(formula, timepoint, mappings)
		}
		else if (formula instanceof BasicLOrImpl) {
			return generateBasicLOr(formula, timepoint, mappings)
		}
		return generateFormula(formula.left as BasicFormula, timepoint, mappings) + ''' \<longrightarrow> ''' + generateFormula(formula.right as BasicFormula, timepoint, mappings)
	}
	
	def static String generatePredicate(BasicPredicate predicate, String timepoint, EList<ProofTermMapping> mappings) {
		return getPredicateName(predicate.basicPredicate) + generateTerms(predicate.params.basicOperands, timepoint, mappings)
	}
	
	def static String generateBasicTermEq(BasicTermEq formula, String timepoint, EList<ProofTermMapping> mappings) {
		return '''«generateTerm(formula.left as BasicTerm, timepoint, mappings)» = «generateTerm(formula.right as BasicTerm, timepoint, mappings)»'''
	}
	
	def static String generateTerms(EList<BasicTerm> terms, String timepoint, EList<ProofTermMapping> mappings) {
		var s = ''''''
		
		for (term: terms) {
			s = s + '''(''' + generateTerm(term, timepoint, mappings) + ''')'''
		}
		
		return s
	}
	
	def static String generateTerm(BasicTerm term, String timepoint, EList<ProofTermMapping> mappings) {
		var s = ''''''
		
		if (term instanceof BasicOperation) {
			s = s + '''«getOperationName(term.contractTrmOperator)» «generateTerms(term.params.basicOperands, timepoint, mappings)»'''
		}
		else {
			if ((term as BasicBaseTerm).portRef instanceof DataTypeVariableImpl) {
				var BasicTerm mappedTerm = null;
				if (mappings !== null && mappings.size() > 0) {
					mappedTerm = getTermFromMappings(((term as BasicBaseTermImpl).portRef as DataTypeVariableImpl).name, mappings)
				}
				
				if (mappedTerm !== null) {
					s = s + '''«generateTerm(mappedTerm, timepoint, null)»'''
				}
				else {
					s = s + '''«((term as BasicBaseTermImpl).portRef as DataTypeVariableImpl).name»'''
				}
			}
			else if ((term as BasicBaseTerm).portRef instanceof OutputPort) {
				s = s + '''«getOutputPortName((term as BasicBaseTermImpl).portRef as OutputPort)»'''
			}
			else {
				s = s + '''«getInputPortName((term as BasicBaseTermImpl).portRef as InputPort)»'''	
			}
			
			if ((term as BasicBaseTerm).portRef instanceof OutputPort || (term as BasicBaseTerm).portRef instanceof InputPort) {
				if (timepoint === null) {
					s = s + ''' (n + 0)'''
				}
				else {
					s = s + ''' (n + ''' + timepoint + ''')'''
				}
			}
		}
		
		return s
	}
	
	def static BasicTerm getTermFromMappings(String varName, EList<ProofTermMapping> mappings) {
		for(ProofTermMapping mapping: mappings) {
			if (mapping.variable.equals(varName)) {
				return mapping.term
			}
		}
		
		return null;
	}
	
	def static String getContractName(Contract contract) {
		return (contract.eContainer as ComponentType).name + "__" + contract.name
	}
	
	def static String generateBasicLAnd(BasicFormula formula, String timepoint, EList<ProofTermMapping> mappings) {
		return generateFormula(formula.left as BasicFormula, timepoint, mappings) + ''' \<and> ''' + generateFormula(formula.right as BasicFormula, timepoint, mappings)
	}
	
	def static String generateBasicLOr(BasicFormula formula, String timepoint, EList<ProofTermMapping> mappings) {
		return generateFormula(formula.left as BasicFormula, timepoint, mappings) + ''' \<or> ''' + generateFormula(formula.right as BasicFormula, timepoint, mappings)
	}
	
	def static String getPredicateName(DTPredicate predicate) {
		return '''«(predicate.eContainer as DataTypeSpec).name»_«predicate.name»''';
	}
	
	def static String getOperationName(Operation operation) {
		return '''«(operation.eContainer as DataTypeSpec).name»_«operation.name»''';
	}
	
	def static String getInputPortName(InputPort port) {
		return '''«(port.eContainer as ComponentType).name»__«port.name»''';
	}
	
	def static String getOutputPortName(OutputPort port) {
		return '''«(port.eContainer as ComponentType).name»__«port.name»''';
	}
	
	def static String getInputPortType(InputPort port) {
		return '''«(port.inputPrtSrtTyp.eContainer as DataTypeSpec).name»_«port.inputPrtSrtTyp.name»''';
	}
	
	def static String generateProofContracts(EList<ProofContract> contracts) {
		if (contracts === null || contracts.size() === 0) {
			return ''''''
		}
		var result = '''begin«"\n"»'''
		
		for(contract: contracts) {
			result += generateProofContract(contract) + '''«"\n"»'''
		}
		
		result += '''end«"\n"»'''
		
		return result
	}
	
	def static String generateProofContract(ProofContract contract) {
		var result = '''theorem «contract.name»:«"\n"»'''
		// fixes
		result += '''«"\t"»fixes n::nat «IF contract.contractDtVar !== null»«FOR variable: contract.contractDtVar» and «variable.name»::«(variable.varSortType.eContainer as DataTypeSpec).name»_«variable.varSortType.name»«ENDFOR»«ENDIF»«"\n"»'''
		if (contract.triggers !== null && contract.triggers.size() > 0) {
			// assumptions
			result += '''«"\t"»assumes «contract.triggers.join("", " and ","", [trigger| '''«trigger.name»: "''' + generateTrigger(trigger) + '''"'''])»«"\n"»'''	
		}
		// shows
		result += '''«"\t"»shows "«generateFormula(contract.guarantees, contract.duration, null)»"«"\n"»'''
		// proofs
		if (contract.proof !== null) {
			result += '''«generateProofSteps(contract)»'''	
		}
		
		return result
	}
	
	def static String generateProofSteps(ProofContract contract) {
		var result = '''proof - «"\n"»'''
		
		for (proofStep: contract.proof.proofSteps) {
			if (proofStep.proofStepRefs === null || proofStep.proofStepRefs.size() === 0) {
				result += '''«"\t"»have «proofStep.name»: "«generateFormula(proofStep.state, proofStep.timepoint, proofStep.proofTermMappings)»" by simp «"\n"»'''
			}
			else {
				var j = 0
				
				for (reference: proofStep.proofStepRefs) {
					if (j !== 0) {
						result += '''«"\t"»moreover from '''
					}
					else {
						result += '''«"\t"»from '''	
					}
					
					if (reference.trigger !== null) {
						result += '''«reference.trigger.name» '''
						var f = (proofStep.contract as Contract).triggers.get(j).formula
						// calculating timepoint for reference: adding the timepoint of the reference
						var t = reference.trigger.timepoint
						
						result += '''have "«generateFormula(f, t, proofStep.proofTermMappings)»" by auto «"\n"»'''
					}
					else {
						var referenceWithConnections = reference as ProofStepRefWithConnections
						result += '''«referenceWithConnections.proofstep.name» '''
						
						var f = (proofStep.contract as Contract).triggers.get(j).formula
						// calculating timepoint for reference: adding the timepoint of the reference
						var t = referenceWithConnections.proofstep.timepoint
						
						result += '''have "«generateFormula(f,t, proofStep.proofTermMappings)»"'''
						if (referenceWithConnections.proofConnections !== null && referenceWithConnections.proofConnections.size() > 0) {
							result += ''' using '''
							for (connection: referenceWithConnections.proofConnections) {
								var c = connection as Connection
								result += '''"«c.name»" '''
							}
						}
						result += '''by auto «"\n"»'''
					}
					j++
				}
				if (j === 1) {
					result += '''«"\t"»hence '''
				}
				else {
					result += '''«"\t"»ultimately have '''
				}
				
				result += '''«proofStep.name»: "«generateFormula(proofStep.state, proofStep.timepoint, null)»" using "«getContractName((proofStep.contract as Contract))»"'''
				if (proofStep.proofBy !== null) {
					result += '''«"\n"»«"\t"»«"\t"» by «proofStep.proofBy.replace('"', '')»«"\n"»'''
				} else {
					result += '''by blast «"\n"»'''
				}
			}
		}
		
		result += '''«"\t"»thus ?thesis by auto«"\n"»qed«"\n"»'''
		return result
	}
	
	def static generateBinary(BinaryOperator binaryOp){
		return '''«IF binaryOp.LImplies == '⇒'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LAnd == '∧'»\<and>\<^sup>c «ENDIF»«IF binaryOp.LDisjunct == '∨'»\<or>\<^sup>c «ENDIF»«IF binaryOp.LDoubleImplies == '⇔'»\<longrightarrow>\<^sup>c «ENDIF»«IF binaryOp.LWeakUntil == 'W'»\<WW>\<^sub>c «ENDIF»«IF binaryOp.LUntil == 'U'»\<UU>\<^sup>c «ENDIF»'''
	}
	
	def static generateUnary(UnaryOperator opvalue){
		return '''«IF opvalue.ltlG == 'G'»\<box>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'F'»\<diamond>\<^sub>c «ENDIF»«IF opvalue.ltlF == 'X'»\<circle>\<^sub>c «ENDIF»'''
	}
	
	def static String addTimepoints(String a, String b) {
		var a1 = 0
		var b1 = 0
		
		if (a !== null) {
			a1 = Integer.parseInt(a)
		}
		
		if (b !== null) {
			b1 = Integer.parseInt(b)
		}
		
		return "" + (a1+b1)
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
		val ctpTerm2CmpTypPrt = ctat.ctaPTerm2.termOperatorFunction.trmOperands.map[(cmpVariableRef.portRef as InputPort).name].toString.replaceAll("[\\[\\],]","")
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
				«ELSEIF ctapval.ctaVal == 'val' && valCmpVarInputPort !== null && ctapval.ctaValTerms.cmpVariableRef !== null && ctapval.ctaValTerms.cmpVariableRef.cmpRef !== null »«val valCmpPortSecondInpt = (ctapval.ctaValTerms.cmpVariableRef.portRef as InputPort).name»«val valCmpTypShortNameSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = ctapval.ctaValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
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
		return '''«IF af instanceof AgBinaryFormulas»«generateFormula(af as AgBinaryFormulas)»«ELSE»«IF af.agBaseTerms !== null»«generateAgBaseTerms(af.agBaseTerms)»«ENDIF»«IF af.agUnaryFormulas !== null»«generateFormula(af.agUnaryFormulas)»«ENDIF»«IF af.agQuantifiedFormulas !== null»«generateFormula(af.agQuantifiedFormulas)»«ENDIF»«IF af.agBinaryFormulas !== null»«generateFormula(af.agBinaryFormulas as AgBinaryFormulas)»«ENDIF»«IF af.agFormulaWithBracket !== null»«generateFormula(af.agFormulaWithBracket)»«ENDIF»«ENDIF»'''
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
		val ctpTerm2CmpTypPrt = agt.agPTerm2.termOperatorFunction.trmOperands.map[(cmpVariableRef.portRef as InputPort).name].toString.replaceAll("[\\[\\],]","")
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
					«ELSEIF agpval.agVal == 'val' && valCmpVarInputPort !== null && agpval.agValTerms.cmpVariableRef !== null && agpval.agValTerms.cmpVariableRef.cmpRef !== null »«val valCmpPortSecondInpt = (agpval.agValTerms.cmpVariableRef.portRef as InputPort).name»«val valCmpTypShortNameSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.cmptypAssigned.ctsname»«val valCmpVarSecondInpt = agpval.agValTerms.cmpVariableRef.cmpRef.name»ca (\<lambda>c. «valCmpTypShortNameSecondInpt»«valCmpPortSecondInpt» («valCmpTypShortNameSecondInpt»cmp «valCmpVarSecondInpt» c) \<in> «valCmpTypShortName»«valCmpVarInputPort.name» («valCmpTypShortName»cmp «valCmpVarFirstInpt» c))«ENDIF»'''
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
}
