package org.tum.factum.pattern.ui.contentassist;

import com.altran.general.integration.xtextsirius.runtime.IXtextLanguageInjector;
import org.tum.factum.pattern.ui.internal.PatternActivator;
import com.google.inject.Injector;

public class LanguageInjector implements IXtextLanguageInjector {
	
	@Override
	public Injector getInjector() {
		return PatternActivator.getInstance().getInjector(PatternActivator.ORG_TUM_FACTUM_PATTERN_PATTERN);
	}

}