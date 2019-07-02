## Manual for Xtext / Sirius integration plugin  
  
1) ### Download the plugin  
  
   In Obeo Designer: Click on  Help in the navigation bar -&gt; Install New Software...  
   Then Paste the following link: https://altran-mde.github.io/xtext-sirius-integration.io/p2/  
   to the Work with: textfield and download the package.  
  
  
2) ### Language Injector  
  
   The Pattern.xtext file needs to be linked with the plugin in order to work properly.   
   To achieve this we need to create a new LanguageInjector class inside of our project.   
   For example you can add the LanguageInjector class to the org.tum.factum.ui.contentassist package.  
   Simply add the LanguageInjector.java file from the example folder to this package.  
  
   Also, we need to add a link to our extension in the plugin.xml file of the org.factum.ui package.  
   For this you need to paste the following xml code to plugin.xml file:  
  
  &lt;extension point="com.altran.general.integration.xtextsirius.runtime.xtextLanguageInjector"&gt;  
    &lt;injector  
      id="org.tum.factum.pattern.ui.contentassist.languageInjectorId"  
      class="org.tum.factum.pattern.ui.contentassist.LanguageInjector"  
    /&gt;  
  &lt;/extension&gt;  
  
  We also need to add the dependency of the plugin to our plugin.xml in the org.factum.ui package.  
  Under the point Dependency add the following plugin: com.altran.general.integration.xtextsirius.runtime;bundle-version="0.18.0"  
  
  The Xtext / Sirius integration should now be integrated to your project.  
  With the id org.tum.factum.pattern.ui.contentassist.languageInjectorId you can use the features of the plugin.  
  
  
User Manual Link: https://altran-mde.github.io/xtext-sirius-integration.io/userguide/ 