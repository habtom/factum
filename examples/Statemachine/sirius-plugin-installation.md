# Manual for Xtext / Sirius integration plug-in  
  
## 1) Download the plug-in  
  
  In Obeo Designer: Click on  **_Help_** in the navigation bar -&gt; **_Install New Software..._**
  Then Paste the following link: https://altran-mde.github.io/xtext-sirius-integration.io/p2/  
  to the **_Work with:_** textfield and download the package.  
  
## 2) Language Injector  
  
  The **Pattern.xtext** file needs to be linked with the plug-in in order to work properly.
  To achieve this we need to create a new LanguageInjector class inside of our project.
  For example you can add the LanguageInjector class to the **org.tum.factum.ui.contentassist** package.  
  Simply add the **LanguageInjector.java** file from the example folder to this package.  
  
  Each Injector needs an Id in order to be referenced from the odesign model. To achieve this we need an extension in our **plugin.xml** file, which can be found inside of the **org.tum.factum.ui** package.  
  Copy and paste the following XML-code to the **plugin.xml** file  
  
  ```xml
  <extension point="com.altran.general.integration.xtextsirius.runtime.xtextLanguageInjector">
    <injector  
      id="org.tum.factum.pattern.ui.contentassist.languageInjectorId"  
      class="org.tum.factum.pattern.ui.contentassist.LanguageInjector"  
    >  
  </extension>
  ```
  
## 3) plug-in Dependency

  The last step is to add the dependency of the plug-in to the **MANIFEST.MF** file.
  As in step 2) navigate to the **plugin.xml** file and click on **_Dependencies_**.
  Then click on **_Add_** and add the following plug-in:
  **_com.altran.general.integration.xtextsirius.runtime;bundle-version="0.18.0"_**

  After all of these steps the Xtext / Sirius integration should be fully configured.  
  With the Id **_org.tum.factum.pattern.ui.contentassist.languageInjectorId_** you can use the features of the plug-in.  
  
### User Manual Link: https://altran-mde.github.io/xtext-sirius-integration.io/userguide/

### GitHub Link: https://github.com/altran-mde/xtext-sirius-integration