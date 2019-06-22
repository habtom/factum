package org.tum.factum.pattern.generator

import java.util.Set
import java.util.HashMap
import java.util.Map.Entry
import java.util.LinkedHashMap
import org.tum.factum.pattern.pattern.BinaryOperator
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
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.Parameter
import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.UnaryOperator
import org.tum.factum.pattern.pattern.PortRef
import java.util.ArrayList

class JavaMOPTextGenerator {
	static String ltlFormula = "";

	// Contains Monitor parameters
	static var args = new LinkedHashMap<String, String>;

	// All possible data types
	static var dataTypes = new HashMap<String, HashMap<String, String>>;

	// All possible events
	static var eventList = new LinkedHashMap<String, String>;

	// All packages from Data Types and Component Types
	static var packageList = new ArrayList<String>;

	static var existOperatorList = new HashMap<String, String>;

	// Main function that converts input to .mop specification.
	def static convertToMOP(Pattern root) {
		// Reset static variables
		ltlFormula = "";
		args = new LinkedHashMap<String, String>;
		dataTypes = new HashMap<String, HashMap<String, String>>;
		eventList = new LinkedHashMap<String, String>;
		packageList = new ArrayList<String>;

		// Get data types from DT-Specifications
		for (dt : root.dtSpec) {
			for (sort : dt.dtSorts) {
				dataTypes.put(sort.name, new HashMap<String, String>());
			}

			for (op : dt.dtOps) {
				dataTypes.get(op.dtInput.get(0).name).put(op.name, op.dtOutput.name);
			}

			// If data type has package name, then insert the package name to "packageName" list.
			if (dt.packageName !== null && !dt.packageName.isEmpty()) {
				packageList.add(dt.packageName);
			}
		}

		// Get packages from Component Types
		for (ct : root.componentTypes) {
			// If data type has package name, then insert the package name to "packageName" list.
			if (ct.packageName !== null && !ct.packageName.isEmpty()) {
				packageList.add(ct.packageName);
			}
		}

		// Read all "ltl_formula" and connect them with "and" if there is more than 1 formula.
		// This also allows us to get Monitor parameters and events.
		try {
			for (cta : root.ctaFormulaIds) {
				ltlFormula += mapFormula(cta.ctaFormula, null);

				// If there is multiple ltl formula add "and" between them.
				if (cta != root.ctaFormulaIds.last()) {
					ltlFormula += " and ";
				}
			}
		} catch (Exception e) {
			e.printStackTrace(System.out);
			System.out.println("Exception occurred: " + e.getMessage());
		}

		// Here program creates/formats .mop specification and returns it
		return '''
««« Java package declaration
package mop;«"\n"»

««« Java library import declarations
import java.io.*;«"\n"»
import java.util.*;«"\n"»
«FOR pckg : packageList»import «pckg»«";\n"»«ENDFOR»

««« Write Specification name and parameters.
«root.name»(«IF args.entrySet().iterator().hasNext()»«args.entrySet().iterator().next().getValue()» «args.entrySet().iterator().next().getKey()»«
»«FOR arg: args.entrySet().drop(1)», «arg.getValue()» «arg.getKey()»«ENDFOR»«ENDIF») {


««« The program already filled "eventList" with events. Here we print all of them.
«FOR event : eventList.entrySet()»
«"\t"»«event.getValue()»
«"\n"»«ENDFOR»

««« LTL formula
«"\t"»ltl: «ltlFormula»«"\n"»

««« LTL violation
«"\t"»@violation { System.out.println("ltl violated!"); }

««« End of MOP specification
}
'''
	}

	// Converts binary operator to LTL type unary operator
	def static generateBinary(BinaryOperator binaryOp) {
		// TODO: 'weak until' operator syntax for LTL
		return '''«IF binaryOp.LImplies == '⇒'»=>«ELSEIF binaryOp.LAnd == '∧'»and«ELSEIF binaryOp.LDisjunct == '∨'»or«ELSEIF binaryOp.LDoubleImplies == '⇔'»<=>«ELSEIF binaryOp.LWeakUntil == 'W'»\<WW>\<^sub>c «ELSEIF binaryOp.LUntil == 'U'»U«ENDIF»'''
	}

	// Converts unary operator to LTL type unary operator
	def static generateUnary(UnaryOperator opvalue) {
		return '''«IF opvalue.ltlG == 'G'»[]«ELSEIF opvalue.ltlF == 'F'»<>«ELSEIF opvalue.ltlX == 'X'»o«ELSEIF opvalue.neg == '¬'»not«ENDIF»'''
	}

	// Map formula to LTL formula
	def static Object mapFormula(CtaFormula cf, Pair<String, String> pair) {
		return '''«IF cf instanceof CtaBinaryFormulas»«generateFormula(cf as CtaBinaryFormulas, pair)»«ELSE»«IF cf.ctaBaseTerms !== null»«generateCtaBaseTerms(cf.ctaBaseTerms, pair)»«ENDIF»«IF cf.ctaUnaryFormulas !== null»«generateFormula(cf.ctaUnaryFormulas, pair)»«ENDIF»«IF cf.ctaQuantifiedFormulas !== null»«generateFormula(cf.ctaQuantifiedFormulas, pair)»«ENDIF»«IF cf.ctaBinaryFormulas !== null»«generateFormula(cf.ctaBinaryFormulas as CtaBinaryFormulas, pair)»«ENDIF»«IF cf.ctaFormulaWithBracket !== null»«generateFormula(cf.ctaFormulaWithBracket, pair)»«ENDIF»«ENDIF»'''
	}

	def static generateCtaBaseTerms(CtaBaseTerms baseTerms, Pair<String, String> pair) {
		return '''«IF baseTerms.ctaPredicateCAct !== null»«generateFormula(baseTerms.ctaPredicateCAct, pair)»«ENDIF»«IF baseTerms.ctaPredicatePAct !== null»«generateFormula(baseTerms.ctaPredicatePAct, pair)»«ENDIF»«IF baseTerms.ctaPredicateTerms !== null»«generateFormula(baseTerms.ctaPredicateTerms, pair)»«ENDIF»«IF baseTerms.ctaPredicateConn !== null»«generateFormula(baseTerms.ctaPredicateConn, pair)»«ENDIF»«IF baseTerms.ctaPredicateVal !== null»«generateFormula(baseTerms.ctaPredicateVal, pair)»«ENDIF»«IF baseTerms.ctaPredicateEq !== null»«generateFormula(baseTerms.ctaPredicateEq, pair)»«ENDIF»'''
	}

	def dispatch static generateFormula(CtaBinaryFormulas ctabf, Pair<String, String> pair) {
		var result = "";
		if (ctabf.binaryOperator !== null) {
			var equalityPair = new Pair<String, String>("", "");
			if (ctabf.binaryOperator.LAnd == '∧' && ctabf.right.ctaBaseTerms !== null &&
				ctabf.right.ctaBaseTerms.ctaPredicateTerms !== null) {
				equalityPair = generateFormula(ctabf.right.ctaBaseTerms.ctaPredicateTerms,
					pair) as Pair<String, String>;
				result += '''«mapFormula(ctabf.left, equalityPair)»''';
			} else if (ctabf.binaryOperator.LAnd == '∧' && ctabf.right.ctaFormulaWithBracket !== null) {
				try {
					var ctaBinaryFormulas = ctabf.right.ctaFormulaWithBracket.ctaPrimaryFormula.
						ctaBinaryFormulas as CtaBinaryFormulas;
					if (ctaBinaryFormulas.ctaPrimary.ctaBaseTerms.ctaPredicateTerms !== null) {
						equalityPair = generateFormula(ctaBinaryFormulas.ctaPrimary.ctaBaseTerms.ctaPredicateTerms,
							pair) as Pair<String, String>;
						result += '''«mapFormula(ctabf.left, equalityPair)»''';
					} else {
						result = '''«mapFormula(ctabf.left, null)» «generateBinary(ctabf.binaryOperator)» «mapFormula(ctabf.right, null)»''';
					}
				} catch (Exception e) {
					result = '''«mapFormula(ctabf.left, null)» «generateBinary(ctabf.binaryOperator)» «mapFormula(ctabf.right, null)»''';
				}

			} else {
				result = '''«mapFormula(ctabf.left, null)» «generateBinary(ctabf.binaryOperator)» «mapFormula(ctabf.right, null)»''';
			}
		}

		if (ctabf.ctaPrimary !== null) {
			result += '''«mapFormula(ctabf.ctaPrimary, pair)»''';
		}

		return result;
	}

	// Generate quantifier operation formula
	def dispatch static generateFormula(CtaQuantifiedFormulas ctaq, Pair<String, String> pair) {
		var result = "";
		if (ctaq.quantifierOperator !== null) {
			if (ctaq.quantifierOperator.exists == '∃') {
				var objectName = ctaq.quantifierOperator.quantifiedExistsVar.name;
				var objectType = ctaq.quantifierOperator.quantifiedExistsVar.cmptypAssigned.name;

				// Add exist operator for 
				existOperatorList.put(objectName, objectType);
				result += mapFormula(ctaq.ctaQuantifiedFs, pair);
				existOperatorList.remove(objectName);
			} else {
				throw new UnsupportedOperationException(ctaq.quantifierOperator +
					" quantified operator is not supported.");
			}
		}

		return result;
	}

	// Convert formula with parentheses to LTL
	def dispatch static generateFormula(CtaFormulaWithBracket fwb, Pair<String, String> pair) {
		return '''«IF fwb.leftBracket == '('»(«ENDIF»«mapFormula(fwb.ctaPrimaryFormula, pair)»«IF fwb.rightBracket == ')'»)«ENDIF»'''
	}

	// Converts unary formulas to LTL
	def dispatch static generateFormula(CtaUnaryFormulas ctau, Pair<String, String> pair) {
		'''«IF ctau.unaryOperator !== null»«generateUnary(ctau.unaryOperator)» «ENDIF»«IF ctau.ctaFormulaLtl !== null»«mapFormula(ctau.ctaFormulaLtl, pair)»«ENDIF»«IF ctau.ctaBaseTerms !== null»«generateCtaBaseTerms(ctau.ctaBaseTerms, pair)»«ENDIF»'''
	}

	def dispatch static Pair<String, String> generateFormula(CtaPredicateTerms ctat, Pair<String, String> pair) {
		if (ctat.equalityOperator !== null) {
			if (ctat.ctaPTerm1.cmpVariableRef !== null && ctat.ctaPTerm2.cmpVariableRef !== null) {
				throw new UnsupportedOperationException("Equality for component variables is not supported.");
			} else if (ctat.ctaPTerm1.dtTypeVars !== null && ctat.ctaPTerm2.dtTypeVars !== null) {
				var leftVar = ctat.ctaPTerm1.dtTypeVars.name;
				var rightVar = ctat.ctaPTerm2.dtTypeVars.name;
				return new Pair<String, String>(leftVar, rightVar);
			} else if (ctat.ctaPTerm1.termOperatorFunction !== null && ctat.ctaPTerm2.termOperatorFunction !== null) {
				if (ctat.ctaPTerm1.termOperatorFunction.trmOperator.name ===
					ctat.ctaPTerm2.termOperatorFunction.trmOperator.name) {
					try {
						var operatorName = ctat.ctaPTerm1.termOperatorFunction.trmOperator.name;
						var leftVar = ctat.ctaPTerm1.termOperatorFunction.trmOperands.get(0).dtTypeVars.name + "_" +
							operatorName;
						var rightVar = ctat.ctaPTerm2.termOperatorFunction.trmOperands.get(0).dtTypeVars.name + "_" +
							operatorName;
						return new Pair<String, String>(leftVar, rightVar);
					} catch (Exception e) {
						return null;
					}
				}
			}
		}
		return null;
	}

	// Convert cAct(...) to LTL event for constructor execution
	def dispatch static generateFormula(CtaPredicateCAct ctapCact, Pair<String, String> pair) {
		if (ctapCact.CAct == 'cAct') {
			var objectType = ctapCact.CActCmpVar.cmptypAssigned.name;
			var objectName = ctapCact.CActCmpVar.name;

			// Event name should be "objectType_cact_objectName".
			// For example: If objectType is "Item" and objectName is "i" => event name will be - "item_cact_i"
			var eventName = objectType.toLowerCase() + "_cact";
			var targetObject = "";
			var eventParameters = "";
			if (existOperatorList.get(objectName) === null) {
				eventName += "_" + objectName;
				targetObject = " && target(" + objectName + ")";
				eventParameters = objectType + " " + objectName;

				// Add event parameter to Monitor argument list
				args.put(objectName, objectType);
			}

			var equalityOperator = getEqualityOperator(pair);

			// Event should look like this:
			// event item_cact_i before(Item i) : execution(* Item.new(..)) && target(i) { }
			if (!eventList.containsKey(eventName)) {
				// Create PAct event
				var event = "event " + eventName + " before(" + eventParameters + ") : \n\t\t" + "execution(* " +
					objectType + "." + "new(..))" + targetObject + " && within(" + objectType + ")" + equalityOperator +
					" { }";

				// Add new event to eventList
				eventList.put(eventName.toLowerCase(), event);
			}

			// Write constructor event name in LTL formula
			'''«eventName»'''
		}
	}

	// Convert pAct(...) to LTL method call/execution event
	def dispatch static generateFormula(CtaPredicatePAct ctapPact, Pair<String, String> pair) {
		if (ctapPact.PAct == 'pAct') {
			var objectType = ctapPact.PActCtaCmpVaref.cmpRef.cmptypAssigned.name;
			var objectName = ctapPact.PActCtaCmpVaref.cmpRef.name;

			// Event name should be "portName_pact_objectName".
			// For example: If portName is "addItem" and objectName is "w" => event name will be - "additem_pact_w"
			var eventName = ctapPact.PActCtaCmpVaref.portRef.name.toLowerCase() + "_pact";
			var targetObject = "";
			var eventParameters = "";

			if (existOperatorList.get(objectName) === null) {
				eventName += "_" + objectName;
				targetObject = " && target(" + objectName + ")";
				eventParameters = objectType + " " + objectName;

				// Add event parameter to Monitor argument list
				args.put(objectName, objectType);
			}

			if (!eventList.containsKey(eventName)) {
				// Create PAct event
				var event = "event " + eventName + " before(" + eventParameters + ") : \n\t\t";

				// If argument of "pAct" is an InputPort, then use "execution"
				// If argument of "pAct" is an OutputPort, then use "call"
				// Else throw IllegalArgumentException
				if (ctapPact.PActCtaCmpVaref.portRef instanceof InputPort) {
					event += "execution";
				} else if (ctapPact.PActCtaCmpVaref.portRef instanceof OutputPort) {
					event += "call";
				} else {
					throw new IllegalArgumentException("Wrong usage of pAct(). Argument must be a port.");
				}

				var equalityOperator = getEqualityOperator(pair);

				event +=
					"(* " + objectType + "." + ctapPact.PActCtaCmpVaref.portRef.name + "(..))" + targetObject +
						" && within(" + objectType + ")" + equalityOperator + " { }";

				// Add new event to eventList
				eventList.put(eventName, event);
			}

			// Write event name in LTL formula
			'''«eventName»'''
		}
	}

	// Convert conn(x.oPort, y.iPort) to LTL method call event
	// The port names should be same
	def dispatch static generateFormula(CtaPredicateConn ctaConn, Pair<String, String> pair) {
		val iPort = ctaConn.ctaConnCmpVarInptPort.inputPrtrf;
		val oPort = ctaConn.ctaConnCmpVarOutputPort.outputPrtrf;
		var oPortObject = ctaConn.ctaConnCmpVarOutputPort.outptPrtCmpRef;
		var oPortObjectType = ctaConn.ctaConnCmpVarOutputPort.outptPrtCmpRef.cmptypAssigned.name;
		var iPortObject = ctaConn.ctaConnCmpVarInptPort.inptPrtCmpRef;
		var iPortObjectType = ctaConn.ctaConnCmpVarInptPort.inptPrtCmpRef.cmptypAssigned.name;

		if (iPort.name.toLowerCase() != oPort.name.toLowerCase()) {
			throw new IllegalArgumentException(
				"Wrong usage of conn() operator. Input port name and Output port name must be same.");
		}

		var eventName = oPort.name.toLowerCase() + "_conn";
		var targetObject = "";
		var eventParameters = "";
		var thisObject = "";

		// If there is no "Exist" operator for outputPortObject
		// Then add outputPortObject as a monitor parameter
		// Else ignore outputPortObject.
		if (existOperatorList.get(oPortObject.name) === null) {
			// Add "oPortObject" to the event name and parameter list
			eventName += "_" + oPortObject.name;
			eventParameters += oPortObjectType + " " + oPortObject.name;

			// Add " && this(oPortObject)" to the AspectJ event
			thisObject = " && this(" + oPortObject.name + ")";

			// Add event parameter to Monitor argument list
			args.put(oPortObject.name, oPortObjectType);
		}

		// If there is no "Exist" operator for inputPortObject
		// Then add inputPortObject as a monitor parameter
		// Else ignore inputPortObject.
		if (existOperatorList.get(iPortObject.name) === null) {
			// Add "iPortObject" to the event name and parameter list
			eventName += "_" + iPortObject.name;
			if (!eventParameters.isEmpty()) {
				eventParameters += ", ";
			}
			eventParameters += iPortObjectType + " " + iPortObject.name;

			// Add " && target(iPortObject)" to the AspectJ event
			targetObject = " && target(" + iPortObject.name + ")";

			// Add event parameter to Monitor argument list
			args.put(iPortObject.name, iPortObjectType);
		}

		var equalityOperator = getEqualityOperator(pair);

		if (!eventList.containsKey(eventName)) {
			var event = "event " + eventName + " before(" + eventParameters + ") : \n\t\t" + "call(* " +
				iPortObject.cmptypAssigned.name + "." + iPort.name + "(..))" + thisObject + targetObject +
				" && within(" + oPortObjectType + ")" + equalityOperator + " { }";

			eventList.put(eventName, event);
		}
		'''«eventName»'''
	}

	// Convert Val(...) to LTL method execution/set event
	def dispatch static generateFormula(CtaPredicateVal ctapVal, Pair<String, String> pair) {
		if (ctapVal.valCmpVariableRef !== null && ctapVal.ctaValTerms !== null) {
			val valCmpPortRef = ctapVal.valCmpVariableRef.portRef;
			val objectName = ctapVal.valCmpVariableRef.cmpRef.name;
			val objectType = ctapVal.valCmpVariableRef.cmpRef.cmptypAssigned.name;
			var parameterName = "";
			var paramsTypes = "";
			var paramsNames = "";

			if (ctapVal.ctaValTerms.dtTypeVars !== null) {
				parameterName = ctapVal.ctaValTerms.dtTypeVars.name;
				paramsNames = parameterName;
				paramsTypes = getTypeName(valCmpPortRef);
			} else if (ctapVal.ctaValTerms.termOperatorFunction !== null) {
				// TODO other types
				parameterName += ctapVal.ctaValTerms.termOperatorFunction.trmOperands.get(0).dtTypeVars.name;
				for (operand : ctapVal.ctaValTerms.termOperatorFunction.trmOperands.drop(1)) {
					parameterName += "_" + operand.dtTypeVars.name;
				}
				paramsNames = parameterName + "_" + ctapVal.ctaValTerms.termOperatorFunction.trmOperator.name;
				paramsTypes = ctapVal.ctaValTerms.termOperatorFunction.trmOperator.dtOutput.name;
			}

			var eventName = valCmpPortRef.name.toLowerCase();
			var event = "";
			var params = parameterName;
			var fullParams = paramsTypes + " " + paramsNames;
			var eventParameters = "";
			var targetObject = "";

			// If there is no "Exist" operator for outputPortObject
			// Then add outputPortObject as a monitor parameter
			// Else ignore outputPortObject.
			if (existOperatorList.get(objectName) === null) {
				// Add "oPortObject" to the event name and parameter list
				eventName += "_" + objectName;
				eventParameters += objectType + " " + objectName + ", ";

				// Add " && this(oPortObject)" to the AspectJ event
				targetObject = " && target(" + objectName + ")";

				// Add event parameter to Monitor argument list
				args.put(objectName, objectType);
			}

			var equalityOperator = getEqualityOperator(pair);

			if (valCmpPortRef instanceof InputPort || valCmpPortRef instanceof OutputPort) {
				var portArgs = getPortArgs(valCmpPortRef);

				// If port argument is Object with multiple parameter fields, then use this fields instead of Object.
				if (portArgs.iterator.hasNext()) {
					params = getParameters(portArgs, false, true, parameterName, "_");
					fullParams = getParameters(portArgs, true, true, parameterName, ", ");
					paramsTypes = getParameters(portArgs, true, false, parameterName, ", ");
					paramsNames = getParameters(portArgs, false, true, parameterName, ", ");

					// Add event parameter to Monitor argument list
					for (arg : portArgs) {
						args.put(parameterName + "_" + arg.getKey(), arg.getValue());
					}
				} else {
					// Add event parameter to Monitor argument list
					args.put(paramsNames, paramsTypes);
				}

				// Create event for port.
				var eventType = "execution";
				if (valCmpPortRef instanceof OutputPort) {
					eventType = "call";
				}

				eventName += "_" + params;
				if (!eventList.containsKey(eventName)) {
					event +=
						"event " + eventName + " before(" + eventParameters + fullParams + ") : \n\t\t" + eventType +
							"(* " + objectType + "." + valCmpPortRef.name + "(" + paramsTypes + ") && args(" +
							paramsNames + ")" + targetObject + " && within(" + objectType + ") " + equalityOperator +
							" { }";

					eventList.put(eventName, event);
				}
			} else {
				// Create event for parameter.
				eventName = "set_" + eventName + "_" + paramsNames;

				if (!eventList.containsKey(eventName)) {
					event +=
						"event " + eventName + " before(" + eventParameters + fullParams + ") : \n\t\t" + "set" + "(" +
							paramsTypes + " " + objectType + "." + valCmpPortRef.name + ") && args(" + paramsNames +
							")" + targetObject + equalityOperator + " { }";

					eventList.put(eventName, event);

					args.put(paramsNames, paramsTypes);
				}
			}

			'''«eventName»'''
		}
	}

	def dispatch static generateFormula(CtaPredicateEq ctapeq, Pair<String, String> pair) {
		throw new UnsupportedOperationException("Uquality is not supported in LTL");
	}

	// Gets the parameters of the Method/Port
	def static Set<Entry<String, String>> getPortArgs(PortRef port) {
		var typeName = getTypeName(port);

		var res = dataTypes.get(typeName);
		if (res !== null) {
			val entrySet = res.entrySet();
			return entrySet;
		}

		return null;
	}

	// Get the name of Port's/Method's parameter type
	def static String getTypeName(PortRef port) {
		var typeName = "";
		if (port instanceof InputPort) {
			if (port.inputPrtSrtTyp !== null) {
				typeName = port.inputPrtSrtTyp.name;
			} else {
				return null;
			}
		} else if (port instanceof OutputPort) {
			if (port.outputPrtSrtTyp !== null) {
				typeName = port.outputPrtSrtTyp.name;
			} else {
				return null;
			}
		} else if (port instanceof Parameter) {
			typeName = port.paramSrtTyp.name;
		}

		return typeName;
	}

	// Get and format method parameters
	// showValue - true if you want to get Parameter names
	// ShowKey - true if you want to get Parameter type names
	// Prefix - String that will be added as a prefix to Parameter names
	// Delimiter - delimiter between set of names and types. Might be ',' or ' ', or '_' and etc.
	def static String getParameters(Set<Entry<String, String>> entrySet, boolean showValue, boolean showKey,
		String namePrefix, String delimiter) {
		var result = "";
		if (entrySet === null) {
			return result;
		}

		if (entrySet.iterator().hasNext()) {
			if (showValue) {
				result += entrySet.iterator().next().getValue();
			}
			if (showKey) {
				if (showValue) {
					result += " ";
				}
				result += namePrefix + "_" + entrySet.iterator().next().getKey();
			}

			for (arg : entrySet.drop(1)) {
				result += delimiter;
				if (showValue) {
					result += " " + arg.getValue();
				}
				if (showKey) {
					if (showValue) {
						result += " ";
					}
					result += namePrefix + "_" + arg.getKey();
				}
			}
		}

		return result;
	}

	def static String getEqualityOperator(Pair<String, String> pair) {
		var equalityOperator = "";
		if (pair !== null) {
			equalityOperator = "&& " + pair.key + " == " + pair.value;
		}

		return equalityOperator;
	}

	def static String getName(PortRef ref) {
		switch ref {
			InputPort: return ref.name
			OutputPort: return ref.name
			Parameter: return ref.name
		}
	}
}
