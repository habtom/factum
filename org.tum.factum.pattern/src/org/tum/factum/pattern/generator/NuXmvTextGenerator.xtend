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
import org.tum.factum.pattern.pattern.BtaOpParam
import org.tum.factum.pattern.pattern.Parenthesis
import org.tum.factum.pattern.pattern.Bracket
import org.tum.factum.pattern.pattern.FsmRef
import org.tum.factum.pattern.pattern.FsmVariable
import org.tum.factum.pattern.pattern.NuXmvDataType
import org.tum.factum.pattern.pattern.BoundedNuXmv
import org.tum.factum.pattern.pattern.BoolNuXmv
import org.tum.factum.pattern.pattern.BtaSUntil
import org.tum.factum.pattern.pattern.BtaWUntil
import java.util.ArrayList
import org.tum.factum.pattern.pattern.BehaviorTraceAssertion
import org.tum.factum.pattern.pattern.FsmVariableType

class NuXmvTextGenerator {

	static var HashMap<String, String> dataTypes
	static var HashMap<String, String> functions
	static var HashMap<String, EList<String>> functionParams
	static var HashMap<Integer, String> guardsLeft
	static var HashMap<String, Integer> sortsUpperBound
	static var HashMap<String, Integer> sortsLowerBound
	static var HashMap<String, Integer> varsUpperBound
	static var HashMap<String, Integer> varsLowerBound
	static var ArrayList<String> ltlFormulasVars
	static var ArrayList<String> ltlFormulasBools

	def static toNuXmv(Pattern root, ComponentType cType) {
		dataTypes = new HashMap<String, String>
		functions = new HashMap<String, String>
		functionParams = new HashMap<String, EList<String>>
		guardsLeft = new HashMap<Integer, String>
		sortsUpperBound = new HashMap<String, Integer>
		sortsLowerBound = new HashMap<String, Integer>
		varsUpperBound = new HashMap<String, Integer>
		varsLowerBound = new HashMap<String, Integer>
		ltlFormulasVars = new ArrayList<String>
		ltlFormulasBools = new ArrayList<String>

		for (dType : root.dtSpec) {
			// Dictionary of DataTypes
			for (sort : dType.mapSorts) {
				dataTypes.put(sort.sortName.name, sort.dataType.convertToString)
				val bd = sort.dataType
				if (bd instanceof BoundedNuXmv) {
					sortsUpperBound.put(sort.sortName.name, Integer.parseInt(bd.upperBound))
					sortsLowerBound.put(sort.sortName.name, Integer.parseInt(bd.lowerBound))
				}
			}
			// Dictionary of functions
			for (func : dType.mapOp) {
				val name = func.op.name
				functions.put(name, func.opFunction)
				functionParams.put(name, func.vars)
			}
		}
		val transitions = cType.transitions
		// Convert every guard
		for (var i = 0; i < transitions.size; i++) {
			val guard = convertLeftFormula(transitions.get(i).guard)
			if(guard !== null) guardsLeft.put(i, guard)
		}
		for (variable : cType.btaDtVar) {
			if (sortsUpperBound.get(variable.varSortType.name) !== null) {
				varsUpperBound.put(variable.name, sortsUpperBound.get(variable.varSortType.name))
				varsLowerBound.put(variable.name, sortsLowerBound.get(variable.varSortType.name))
			}
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
			-- Variables
			«val variables = cType.fsmVars»
			«FOR variable : variables»
				«var name = variable.name»
				«var type = variable.varSortType.name»
				«name» : «dataTypes.get(type)»;
			«ENDFOR»
			-- InputPorts
			«val inputPorts = cType.inputPorts»
			«FOR inputPort : inputPorts»
				«var name = inputPort.name»
				«var type = inputPort.inputPrtSrtTyp.name»
				«name» : «dataTypes.get(type)»;
				«name»_noVal : boolean;
			«ENDFOR»
			-- OutputPorts
			«val outputPorts = cType.outputPorts»
			«FOR outputPort : outputPorts»
				«var name = outputPort.name»
				«var type = outputPort.outputPrtSrtTyp.name»
				«name» : «dataTypes.get(type)»;
				«name»_noVal : boolean;
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
			«"\t"»TRUE: state;
			esac;
			
			«FOR variable : variables»
				«transitionVariable(variable.name, transitions)»
				
			«ENDFOR»
			«FOR outputPort : outputPorts»
				«transitionOutputPort(outputPort.name, transitions)»
				
			«ENDFOR»
		«FOR ltlFormula : cType.behaviorTraceAssertion»
			«convertLTLFormula(ltlFormula)»
		«ENDFOR»
		«FOR ltlFormula : ltlFormulasVars»
			«ltlFormula»
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

	def static String initVarToNuXmv(FsmVariableType type, InitDataTypes idt) {
		if (idt.variable !== null) {
			return '''init(«type.name») := «idt.variable.name»;'''
		}
		if (idt.op !== null) {
			val op = idt.op
			return '''init(«type.name») := «getFunction(op.op.name, op.params)»;'''
		}
		return ""
	}

	def static String transitionState(Transition transition, int transitionNr) {
		val transitionStart = transition.transitionStart.name
		val transitionEnd = transition.transitionEnd.name
		val guard = guardsLeft.get(transitionNr)

		return '''state = «transitionStart»«IF (guard != "")» & («guard»)«ENDIF» : «transitionEnd»;'''
	}

	def static String transitionVariable(String variable, EList<Transition> transitions) {
		var right = new HashMap<Integer, String>
		for (var transitionNr = 0; transitionNr < transitions.size; transitionNr++) {
			val action = convertRightFormula(transitions.get(transitionNr).action, variable)
			if(!action.isEmpty) right.put(transitionNr, action)
		}
		if (right.isEmpty) {
			return '''next(«variable») := «variable»;'''
		}

		return '''
			«var transitionNr = 0»
			next(«variable») := case
			«FOR transition : transitions»
				«val action = right.get(transitionNr++)»
				«IF action !== null»
					«"\t"»«build(transition.transitionStart.name, action, transitionNr)»
				«ENDIF»
			«ENDFOR»	
				TRUE: «variable»;
			esac;
		'''
	}

	def static String transitionOutputPort(String outputPort, EList<Transition> transitions) {
		var right = new HashMap<Integer, String>
		for (var transitionNr = 0; transitionNr < transitions.size; transitionNr++) {
			val action = convertRightFormula(transitions.get(transitionNr).action, outputPort)
			if(!action.isEmpty) right.put(transitionNr, action)
		}
		if (right.isEmpty) {
			return '''
				next(«outputPort») := «outputPort»;
				next(«outputPort»_noVal) := TRUE;
			'''
		}

		return '''
			«var transitionNr = 0»
			next(«outputPort») := case
			«FOR transition : transitions»
				«val action = right.get(transitionNr++)»
				«IF action !== null»
					«"\t"»«build(transition.transitionStart.name, action, transitionNr)»
				«ENDIF»
			«ENDFOR»	
				TRUE: «outputPort»;
			esac;
			«var transNr = 0»
			«"\n"»
			next(«outputPort»_noVal) := case
			«FOR transition : transitions»
				«val action = right.get(transNr++)»
				«IF action !== null»
					«"\t"»«build(transition.transitionStart.name, "FALSE", transNr)»
				«ENDIF»
			«ENDFOR»	
				TRUE: TRUE;
			esac;
		'''
	}

	def static String build(String state, String action, int transitionNr) {
		val guard = guardsLeft.get(transitionNr - 1)
		return '''state = «state»«IF (!guard.isEmpty)» & «guard»«ENDIF» : «action»;'''
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
			case formula.noVal !== null:
				return "_"
			FsmLAndImpl:
				return convertLeftFormula(formula.left) + " & " + convertLeftFormula(formula.right)
			ComparisonImpl:
				return convertLeftFormula(formula.left) + formula.comp + convertLeftFormula(formula.right)
			FsmLOr:
				return convertLeftFormula(formula.left) + " | " + convertLeftFormula(formula.right)
			FsmLImp:
				return convertLeftFormula(formula.left) + " -> " + convertLeftFormula(formula.right)
			LogicNeg:
				return "!" + convertLeftFormula(formula.fsmPrimary)
			MathNeg:
				return "-" + convertLeftFormula(formula.fsmPrimary)
			Bracket:
				return "(" + convertLeftFormula(formula.fsmFormula) + ")"
			FsmEquality: {
				val symbol = if(formula.eq === null) "!" else "="
				val lhs = convertLeftFormula(formula.left)
				val rhs = convertLeftFormula(formula.right)
				if(rhs == "_") return lhs + "_noVal"
				if(lhs == "_") return rhs + "_noVal"
				return lhs + symbol + rhs
			}
			default:
				return ""
		}
	}

	// Converts to btaFormula and stores variables in an array
	def static String convertToBtaFormula(BtaFormula formula, ArrayList<String> dtTypes) {
		switch formula {
			BtaLImp:
				return convertToBtaFormula(formula.left, dtTypes) + " -> " + convertToBtaFormula(formula.right, dtTypes)
			BtaLOr:
				return convertToBtaFormula(formula.left, dtTypes) + " | " + convertToBtaFormula(formula.right, dtTypes)
			BtaLAnd:
				return convertToBtaFormula(formula.left, dtTypes) + " & " + convertToBtaFormula(formula.right, dtTypes)
			LTLOperators:
				return (formula.ltlG ?: formula.ltlF ?: formula.ltlX) + convertToBtaFormula(formula.btaFormula, dtTypes)
			BtaTerm:
				return btaTerm(formula)
			Neg:
				return "!" + convertToBtaFormula(formula.btaFormula, dtTypes)
			Parenthesis:
				return "(" + convertToBtaFormula(formula.btaFormula, dtTypes) + ")"
			BtaSUntil:
				return convertToBtaFormula(formula.left, dtTypes) + " U " + convertToBtaFormula(formula.right, dtTypes)
			BtaWUntil: {
				val lhs = convertToBtaFormula(formula.left, dtTypes)
				val rhs = convertToBtaFormula(formula.right, dtTypes)
				return '''«rhs» V («rhs» | «lhs»)'''
			}
			BtaTermEq: {
				val noValPorts = new StringBuilder
				val lhs = btaTerm(formula.left)
				val rhs = btaTerm(formula.right)
				if (formula.left.isPort) {
					noValPorts.append(" & !" + lhs + "_noVal")
				}
				if (formula.right.isPort) {
					noValPorts.append(" & !" + rhs + "_noVal")
				}
				if (formula.left.isDtVar) {
					dtTypes.add(lhs)
				}
				if (formula.right.isDtVar) {
					dtTypes.add(rhs)
				}
				return lhs + "=" + rhs + noValPorts
			}
			default:
				return ""
		}
	}

	def static String btaFunction(String name, BtaOpParam input) {
		var func = functions.get(name)
		if (input === null) {
			return func
		}
		val iteratorParams = functionParams.get(name).iterator
		val iteratorInput = input.btaOperands.iterator

		while (iteratorInput.hasNext && iteratorParams.hasNext) {
			val param = iteratorParams.next
			val term = iteratorInput.next
			func = func.replaceAll(param, btaTerm(term))
		}
		return "(" + func + ")"
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
				return "(" + convertRightFormula(formula.left, variable) + ") | (" +
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
			Bracket:
				return "(" + convertRightFormula(formula.fsmFormula, variable) + ")"
		}
		return ""
	}

	def static void convertLTLFormula(BehaviorTraceAssertion ltlFormula) {
		var fsmVariables = new ArrayList<String>
		val formula = convertToBtaFormula(ltlFormula.btaFormula, fsmVariables)
		val boolVars = new ArrayList<String>()
		val variables = new ArrayList<String>()
		val bools = new ArrayList<Integer>()
		val upperBounds = new ArrayList<Integer>()
		val lowerBounds = new ArrayList<Integer>()
		for (variable : fsmVariables) {
			val upperBound = varsUpperBound.get(variable)
			val lowerBound = varsLowerBound.get(variable)
			// Boolean
			if (upperBound === null) {
				boolVars.add(variable)
				bools.add(1)
			} else {
				upperBounds.add(upperBound)
				lowerBounds.add(lowerBound)
				variables.add(variable)
			}
		}
		if (boolVars.length > 0) {
			val int[] countersBool = newIntArrayOfSize(boolVars.length)
			val int[] countersVar = newIntArrayOfSize(variables.length)
			val int[] lowerBools = newIntArrayOfSize(boolVars.length)
			nestedLoopOperation(lowerBools, countersBool, bools, 0, boolVars, formula, false)
			for (btaFormula : ltlFormulasBools) {
				nestedLoopOperation(lowerBounds, countersVar, upperBounds, 0, variables, btaFormula, true)
			}
		} else {
			val int[] counters = newIntArrayOfSize(variables.length)
			nestedLoopOperation(lowerBounds, counters, upperBounds, 0, fsmVariables, formula, true)
		}
	}

	def static void nestedLoopOperation(int[] lowerBound, int[] counters, int[] length, int level, ArrayList<String> arr, String formula,
		boolean isVar) {
		if (level == counters.length) {
			if(isVar) changeVarToInts(counters, arr, formula) else changeVarToBools(counters, arr, formula)
		} else {
			for (counters.set(level, lowerBound.get(level)); counters.get(level) <= length.get(level); counters.set(level,
				counters.get(level) + 1)) {
				nestedLoopOperation(lowerBound, counters, length, level + 1, arr, formula, isVar)
			}
		}
	}

	def static void changeVarToInts(int[] counters, ArrayList<String> arr, String btaFormula) {
		var formula = "LTLSPEC " + btaFormula
		for (var level = 0; level < counters.length; level++) {
			formula = formula.replaceAll(arr.get(level), counters.get(level).toString)
		}
		ltlFormulasVars.add(formula)
	}

	def static void changeVarToBools(int[] counters, ArrayList<String> arr, String btaFormula) {
		var counterAsString = btaFormula
		for (var level = 0; level < counters.length; level++) {
			counterAsString = counterAsString.replaceAll(arr.get(level),
				if(counters.get(level) == 0) "FALSE" else "TRUE")
		}
		ltlFormulasBools.add(counterAsString)
	}

	def static String btaTerm(BtaTerm term) {
		switch term {
			BtaBaseTerm: return term.btaRef.name
			BtaOperation: return btaFunction(term.btaTrmOperator.name, term.params)
		}
	}

	def static String getName(FsmVariableType variable) {
		switch variable {
			DataTypeVariable: return variable.name
			OutputPort: return variable.name
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

	def static String getName(FsmRef variable) {
		switch variable {
			InputPort: return variable.name
			OutputPort: return variable.name
			Parameter: return variable.name
			FsmVariable: return variable.name
		}
	}

	def static String convertToString(NuXmvDataType dt) {
		switch dt {
			BoundedNuXmv: return '''«dt.lowerBound» .. «dt.upperBound»'''
			BoolNuXmv: return "boolean"
		}
	}

	def static Boolean isPort(BtaTerm term) {
		if (term instanceof BtaBaseTerm) {
			if (term.btaRef instanceof InputPort || term.btaRef instanceof OutputPort)
				return true
		}
		return false;
	}

	def static Boolean isDtVar(BtaTerm term) {
		if (term instanceof BtaBaseTerm) {
			if (term.btaRef instanceof DataTypeVariable)
				return true
		}
		return false;
	}
}
