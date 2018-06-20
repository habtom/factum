package org.tum.factum.pattern.generator

import org.tum.factum.pattern.pattern.Pattern

class Auxiliary {
    def static getInputPorts(Pattern root) {
		return root.componentTypes.map[ct|ct.inputPorts]
	}
	def static getOutputPorts(Pattern root) {
		return root.componentTypes.map[ct|ct.outputPorts]
	}


}