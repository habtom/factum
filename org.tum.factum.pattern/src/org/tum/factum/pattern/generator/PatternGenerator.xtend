/*
 * generated by Xtext 2.12.0
 */
package org.tum.factum.pattern.generator

import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.AbstractGenerator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.generator.IGeneratorContext
import org.tum.factum.pattern.pattern.Pattern

/**
 * Generates code from your model files on save.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#code-generation
 */
class PatternGenerator extends AbstractGenerator {

	override void doGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		val root = resource.allContents.head as Pattern;
		 
		if (root !== null) {
			//For Isabelle
//			fsa.generateFile(root.name + ".thy", IsabelleTextGenerator.toIsabelle(root))
			//For JavaMOP
//			fsa.generateFile(root.name + ".mop", JavaMOPTextGenerator.convertToMOP(root))
			//For nuXmv
			for (var i = 0; i < root.componentTypes.size; i++) {
				val cType = root.componentTypes.get(i)
				if (!cType.states.isEmpty) {
					fsa.generateFile(cType.name + ".smv", NuXmvTextGenerator.toNuXmv(root, cType))
				}
			}
		}

	}
}
