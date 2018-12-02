# FACTum Studio
[//]: # (Architectural Design Constraints Specification and Verification)

FACTum Studio is a tool that supports Architectural Design Patterns (ADPs) specification and verification with the support of interactive verification in Isabelle/HOL.

At this stage of development, the tool has the following key features mainly for specification of ADPs:
* Specification of abstract data types
* Graphical modeling of component types
* Specification of architectural constraints 
* Specification of architectural guarantees and
* Generation of Isabelle/HOL theory from ADP specification.

The tool is developed using the Eclipse Modeling Framework (EMF), which includes Sirius, Xtext, and Xtend.  

A working copy of Obeo Designer Community edition should enable the importing of the FACTum tool metamodel project and runtime sample to start and try the tool. You may download files required from the following links:

* [Download Eclipse, Obeo Designer](https://www.obeodesigner.com/en/download) *(Needs installing Obeo Designer Community Extensions including Xtext)*

* [Download FACTum Metamodel Project and Runtime Application](https://goo.gl/fgZN2Y) *(Contains files 'metamodelFACTumS.zip' and 'runtimeFACTumS.zip' )*
  * First, import the project file *'metamodelFACTumS.zip'* into your Obeo Designer Community workspace, 
  * Then, generate Xtext Artifacts from the file Pattern.xtext. 
  * Next, configure an Eclipse runtime application *(e.g., runtimeFACTumS)* to launch the tool's application demo and then
  * Import the file *'runtimeFACTumS.zip'* into your created Eclipse application (runtimeFACTumS) to try and test the FACTum demo.
  * Verify the example code generated by copying the proof from the file *'factum/examples/PublisherSubscriber.thy'* into the generated Isabelle code.
  
## Publish-subscribe pattern tutorial

The video tutorial below provides a brief overview of using FACTum Studio. The tutorial demonstrates the tool with a specification of the publish-subscribe pattern and transforms the specification to Isabelle/HOL for verification.

[![Publish-subscribe pattern tutorial](https://img.youtube.com/vi/OgJUhAG_4WI/hqdefault.jpg)](http://www.youtube.com/watch?v=OgJUhAG_4WI&t=2275s)

