package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.Pattern
import org.tum.factum.pattern.pattern.ComponentType
import java.util.List
import java.util.ArrayList
import org.tum.factum.pattern.pattern.InputPort
import org.tum.factum.pattern.pattern.OutputPort

class Auxiliary {
	def static List<InputPort> getInputPorts(Pattern root) {
		var List<InputPort>  inputportlist = new ArrayList<InputPort>()
				for (ComponentType ct : root.componentTypes) {
					inputportlist.add(ct.inputports)
				}
				return inputportlist;

	}

	
}