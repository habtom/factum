package org.tum.factum.pattern.generator

import java.util.HashMap
import java.util.stream.Collectors
import java.util.Iterator
import org.eclipse.emf.common.util.EList
import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.InitDataTypes
import org.tum.factum.pattern.pattern.ComponentType
import org.tum.factum.pattern.pattern.DataTypeVariable
import org.tum.factum.pattern.pattern.Transition
import org.tum.factum.pattern.pattern.FsmFormula
import org.tum.factum.pattern.pattern.impl.FsmLAndImpl
import org.tum.factum.pattern.pattern.impl.ComparisonImpl
import org.tum.factum.pattern.pattern.impl.EqualsImpl
import org.tum.factum.pattern.pattern.FsmLOr
import org.tum.factum.pattern.pattern.FsmLImp
import org.tum.factum.pattern.pattern.FsmEquality
import org.tum.factum.pattern.pattern.BtaFormula
import org.tum.factum.pattern.pattern.BtaLImp
import org.tum.factum.pattern.pattern.BtaLOr
import org.tum.factum.pattern.pattern.BtaLAnd
import org.tum.factum.pattern.pattern.BtaTerm
import org.tum.factum.pattern.pattern.LTLOperators
import org.tum.factum.pattern.pattern.BtaTermEq
import org.tum.factum.pattern.pattern.BtaOperation
import org.tum.factum.pattern.pattern.Neg
import org.tum.factum.pattern.pattern.LogicNeg
import org.tum.factum.pattern.pattern.MathNeg
import org.tum.factum.pattern.pattern.BtaBaseTerm
import org.tum.factum.pattern.pattern.OperationDataType
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.Parameter
import org.tum.factum.pattern.pattern.BtaRef

class NuXmvTextGenerator {

	static var dataTypes = new HashMap<String, String>;

	static var functions = new HashMap<String, String>;

	static var functionParams = new HashMap<String, EList<String>>

	static var guardsLeft = new HashMap<Integer, String>

	def static toNuXmv(Pattern root, ComponentType cType) {
		for (dType : root.dtSpec) {
			// Store every mapped datatype in a dictionary
			for (sort : dType.mapSorts) {
				dataTypes.put(sort.sortName.name, sort.dataType)
			}
			for (func : dType.mapOp) {
				val name = func.op.name
				functions.put(name, func.opFunction)
				functionParams.put(name, func.vars)
			}
		}
		val transitions = cType.transitions
		for (var i = 0; i < transitions.size; i++) {
			val guardLeft = convertLeftFormula(transitions.get(i).guardLeft)
			if(guardLeft !== null) guardsLeft.put(i, guardLeft)
		}
		convertToNuXmv(cType)
	}

	def static convertToNuXmv(ComponentType cType) '''
		«val states = cType.states.stream.map[n | n.name].collect(Collectors.joining(",", "{" , "};"))»
		«val transitions = cType.transitions»
		-- Instructions:
		-- ~$ nuXmv -int «cType.name».smv
		-- > go
		-- > check_ltlspec
		
		MODULE main
			
		VAR 
			state : «states»
			«val variables = cType.btaDtVar»
			«FOR variable : variables»
				«var name = variable.name»
				«var type = variable.varSortType.name»
				«name» : «dataTypes.get(type)»;
			«ENDFOR»
			«val inputPorts = cType.inputPorts»
			«FOR inputPort : inputPorts»
				«var name = inputPort.name»
				«var type = inputPort.inputPrtSrtTyp.name»
				«name» : «dataTypes.get(type)»;
			«ENDFOR»
			«val outputPorts = cType.outputPorts»
			«FOR outputPort : outputPorts»
				«var name = outputPort.name»
				«var type = outputPort.outputPrtSrtTyp.name»
				«name» : «dataTypes.get(type)»;
			«ENDFOR»
			
		ASSIGN
			«val init = cType.initial»
			init(state) := «init.initialState.name»;
			«val initVars = init.vars»
			«val Iterator<InitDataTypes> iter = init.dataTypes.iterator»
			«FOR initVar : initVars»
				«IF iter.hasNext»
					«initVarToNuXmv(initVar, iter.next)»
				«ENDIF»
			«ENDFOR»
			
			next(state) := case
			«var transitionNr = 0»
			«FOR transition : transitions»
				«"\t"»«transitionState(transition, transitionNr++)»
			«ENDFOR»
			TRUE: state;
			esac;
			
			«FOR variable : variables»
				«transitionVariable(variable.name, transitions)»
				
			«ENDFOR»
			«FOR inputPort : inputPorts»
				«transitionVariable(inputPort.name, transitions)»
				
			«ENDFOR»
			«FOR outputPort : outputPorts»
				«transitionVariable(outputPort.name, transitions)»
				
			«ENDFOR»
		«FOR ltlFormula : cType.behaviorTraceAssertion»
			LTLSPEC «convertLTLFormula(ltlFormula.btaFormula)»
		«ENDFOR»
	'''

	def static String getFunction(String name, EList<OperationDataType> input) {
		var func = functions.get(name)
		val iteratorParams = functionParams.get(name).iterator
		val iteratorInput = input.iterator

		while (iteratorInput.hasNext && iteratorParams.hasNext) {
			val param = iteratorParams.next
			val dt = iteratorInput.next
			func = func.replaceAll(param, dt.primitive ?: dt.variable.name)
		}
		return func
	}

	def static String initVarToNuXmv(DataTypeVariable dtv, InitDataTypes idt) {
		if (idt.variable !== null) {
			return '''init(«dtv.name») := «idt.variable.name»;'''
		}
		if (idt.op !== null) {
			val op = idt.op
			return '''init(«dtv.name») := «getFunction(op.op.name, op.params)»;'''
		}
		return ""
	}

	def static String getName(BtaRef variable) {
		switch variable {
			InputPort: return variable.name
			OutputPort: return variable.name
			Parameter: return variable.name
			DataTypeVariable: return variable.name
		}
	}

	def static String transitionState(Transition transition, int transitionNr) {
		val transitionStart = transition.transitionStart.name
		val transitionEnd = transition.transitionEnd.name
		val guard = guardsLeft.get(transitionNr)

		return '''(state = «transitionStart»)«IF (guard != "")» & «guard»«ENDIF» : «transitionEnd»;'''
	}

	def static String transitionVariable(String variable, EList<Transition> transitions) {
		var right = new HashMap<Integer, String>
		for (var transitionNr = 0; transitionNr < transitions.size; transitionNr++) {
			val guardRight = convertRightFormula(transitions.get(transitionNr).guardRight, variable)
			if(!guardRight.isEmpty) right.put(transitionNr, guardRight)
		}
		if (right.isEmpty) {
			return '''next(«variable») := «variable»;'''
		}

		return '''
			«var transitionNr = 0»
			next(«variable») := case
			«FOR transition : transitions»
				«val guardRight = right.get(transitionNr++)»
				«IF guardRight !== null»
					«"\t"»«build(transition.transitionStart.name, guardRight, transitionNr)»
				«ENDIF»
			«ENDFOR»	
				TRUE: «variable»;
			esac;
		'''
	}

	def static String build(String state, String guardRight, int transitionNr) {
		val guardLeft = guardsLeft.get(transitionNr - 1)
		return '''(state = «state»)«IF (!guardLeft.isEmpty)» & «guardLeft»«ENDIF» : «guardRight»;'''
	}

	def static String convertLeftFormula(FsmFormula formula) {
		switch formula {
			case null:
				return ""
			case formula.func !== null:
				return "(" + getFunction(formula.func.op.name, formula.func.params) + ")"
			case formula.primitive !== null:
				return formula.primitive
			case formula.variable !== null:
				return formula.variable.name
			FsmLAndImpl:
				return convertLeftFormula(formula.left) + " & " + convertLeftFormula(formula.right)
			ComparisonImpl:
				return "(" + convertLeftFormula(formula.left) + formula.comp + convertLeftFormula(formula.right) + ")"
			FsmLOr:
				return convertLeftFormula(formula.left) + " | " + convertLeftFormula(formula.right)
			FsmLImp:
				return "(" + convertLeftFormula(formula.left) + ") -> (" + convertLeftFormula(formula.right) + ")"
			LogicNeg:
				return "!(" + convertLeftFormula(formula.fsmPrimary) + ")"
			MathNeg:
				return "-" + convertLeftFormula(formula.fsmPrimary)
			FsmEquality: {
				val symbol = if(formula.eq === null) "!" else "="
				return "(" + convertLeftFormula(formula.left) + symbol + convertLeftFormula(formula.right) + ")"
			}
			default:
				return ""
		}
	}

	def static String convertLTLFormula(BtaFormula formula) {
		switch formula {
			BtaLImp: return "(" + convertLTLFormula(formula.left) + ") -> (" + convertLTLFormula(formula.right) + ")"
			BtaLOr: return convertLTLFormula(formula.left) + " | " + convertLTLFormula(formula.right)
			BtaLAnd: return convertLTLFormula(formula.left) + " & " + convertLTLFormula(formula.right)
			LTLOperators: return (formula.ltlG ?: formula.ltlF ?: formula.ltlX) + convertLTLFormula(formula.btaFormula)
			BtaTermEq: return "(" + btaTerm(formula.left) + "=" + btaTerm(formula.right) + ")"
			BtaTerm: return btaTerm(formula)
			Neg: return "!(" + convertLTLFormula(formula.btaFormula) + ")"
		}
	}

	def static String btaTerm(BtaTerm term) {
		switch term {
			BtaBaseTerm: return term.btaRef.name
			BtaOperation: return btaFunction(term.btaTrmOperator.name, term.params.btaOperands)
		}
	}

	def static String btaFunction(String name, EList<BtaTerm> input) {
		var func = functions.get(name)
		val iteratorParams = functionParams.get(name).iterator
		val iteratorInput = input.iterator

		while (iteratorInput.hasNext && iteratorParams.hasNext) {
			val param = iteratorParams.next
			val term = iteratorInput.next
			func = func.replaceAll(param, btaTerm(term))
		}
		return func
	}

	def static String convertRightFormula(FsmFormula formula, String variable) {
		switch formula {
			case null:
				return ""
			case formula.func !== null:
				return "(" + getFunction(formula.func.op.name, formula.func.params) + ")"
			case formula.primitive !== null:
				return formula.primitive
			case formula.variable !== null:
				return formula.variable.name
			FsmLAndImpl: {
				val left = convertRightFormula(formula.left, variable)
				val right = convertRightFormula(formula.right, variable)
				if (left.isEmpty) {
					return convertRightFormula(formula.right, variable)
				}
				if (right.isEmpty) {
					return convertRightFormula(formula.left, variable)
				}
				return convertRightFormula(formula.left, variable) + " & " +
					convertRightFormula(formula.right, variable)
			}
			ComparisonImpl: {
				val left = convertRightFormula(formula.left, variable)
				val right = convertRightFormula(formula.right, variable)
				if (!right.isEmpty && !left.isEmpty) {
					return "(" + left + formula.comp + right + ")"
				}
			}
			EqualsImpl: {
				if (formula.left.variable.name == variable) {
					return convertRightFormula(formula.right, variable)
				}
			}
			FsmLOr: {
				val left = convertRightFormula(formula.left, variable)
				val right = convertRightFormula(formula.right, variable)
				if (left.isEmpty) {
					return convertRightFormula(formula.right, variable)
				}
				if (right.isEmpty) {
					return convertRightFormula(formula.left, variable)
				}
				return "(" + convertRightFormula(formula.left, variable) + ") || (" +
					convertRightFormula(formula.right, variable) + ")"
			}
			FsmLImp: {
				val left = convertRightFormula(formula.left, variable)
				val right = convertRightFormula(formula.right, variable)
				if (!right.isEmpty && !left.isEmpty) {
					return "(" + left + "->" + right + ")"
				}
			}
			LogicNeg:
				return "!(" + convertRightFormula(formula.fsmPrimary, variable) + ")"
			MathNeg:
				return "-" + convertRightFormula(formula.fsmPrimary, variable)
		}
		return ""
	}
}