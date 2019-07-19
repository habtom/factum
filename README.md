# FACTum Studio
[//]: # (Architectural Design Constraints Specification and Verification)

### Contents
**[Overview](#overview)**<br>
**[FACTum Studio Architecture](#factum-studio-architecture)**<br>
**[Installation Instructions](#installation-instructions)**<br>
**[Publish-subscribe Pattern Tutorial](#publish-subscribe-pattern-tutorial)**<br>

## Overview 

FACTum Studio is a tool that supports Architectural Design Patterns (ADPs) specification and verification with the support of interactive verification in Isabelle/HOL.

At this stage of development, the tool has the following key features mainly for specification of ADPs:
* Specification of abstract data types
* Graphical modeling of component types
* Specification of architectural constraints
* Specification of architectural guarantees and
* Generation of Isabelle/HOL theory from ADP specification.

## FACTum Studio Architecture
FACTum Studio is developed using the Eclipse Modeling Framework (EMF), particularly, with [Obeo](https://www.obeo.fr/en/)'s free and ready-to-use Eclipse package Obeo Designer Community edition.
The development of the tool utilizes frameworks and languages in the Eclipse/EMF ecosystem, which include Xtext, Ecore, Xtend and Sirius.
Xtext is a language engineering framework that enables the textual feature of DSL using the base grammar within the EMF.
The Xtend language is an expressive dialect of Java for productivity.
It is used as a programing lanaguage for the additional language features such as type checking, validation, referencing and scoping.

## Installation Instructions

A working copy of Obeo Designer Community edition should enable the importing of the FACTum tool metamodel project and runtime sample to start and try the tool. Currently, FACTum Studio works with Obeo Designer Community Version 10.1. Other versions may not run as expected. You may download files required from the following links:

* [Download Eclipse, Obeo Designer](https://www.obeodesigner.com/en/download) *(Needs installing Obeo Designer Community Edition Extensions including Xtext)*

  * First, extract the downloaded Obeo Designer Community zip file into a directory where you would intend to run it.
  * Next, go to the extracted directory and run the file 'obeodesigner' which is the program launcher.
  * Then, when the program is open and running, install required plugins - Help menu -> Install New Software, these are plugins such as the 'Sirius Integration with Xtext' and 'Xtext Complete SDK' from the Obeo Designer Community Edition Extensions.

* [Download FACTum Metamodel Project and Runtime Application](https://goo.gl/fgZN2Y) *(Contains files 'metamodelFACTumS.zip' and 'runtimeFACTumS.zip' )*
  * First, import the project file *'metamodelFACTumS.zip'* into your Obeo Designer Community workspace,
  * Then, generate Xtext Artifacts from the file Pattern.xtext.
  * Next, configure an Eclipse runtime application *(e.g., runtimeFACTumS)* to launch the tool's application demo and then
  * Import the file *'runtimeFACTumS.zip'* into your created Eclipse application (runtimeFACTumS) to try and test the FACTum demo.
  * Verify the example code generated by copying the proof from the file *'factum/examples/PublisherSubscriber.thy'* into the generated Isabelle code.

## Publish-subscribe Pattern Tutorial

The video tutorial below shows a brief overview of using FACTum Studio. The tutorial demonstrates the tool with a specification of the publish-subscribe pattern and transforms the specification to Isabelle/HOL for verification.

[![Publish-subscribe pattern tutorial](https://img.youtube.com/vi/Q_R17k1ebDY/mqdefault.jpg)](https://youtu.be/Q_R17k1ebDY)
