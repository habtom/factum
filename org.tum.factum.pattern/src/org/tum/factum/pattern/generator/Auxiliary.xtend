package org.tum.factum.pattern.generator

import java.util.List
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.OutputPort
import org.tum.factum.pattern.pattern.Pattern

class Auxiliary {
    def static List<InputPort> getInputPorts(Pattern root) {
		return root.componentTypes.map[ct|ct.inputports]
	}
	def static List<OutputPort> getOutputPorts(Pattern root) {
		return root.componentTypes.map[ct|ct.outputports]
	}
	
//	def static List<InputPort> getInputPorts(Pattern root) {
//		var List<InputPort>  inputportlist = new ArrayList<InputPort>()
//				for (ComponentType ct : root.componentTypes) {
//					inputportlist.add(ct.inputports)
//				}
//				return inputportlist;
//
//	}
//	def static List<OutputPort> getOutputPorts(Pattern root) {
//		var List<OutputPort>  outputportlist = new ArrayList<OutputPort>()
//				for (ComponentType ct : root.componentTypes) {
//					outputportlist.add(ct.outputports)
//				}
//				return outputportlist;
//
//	}

}