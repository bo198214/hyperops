VERSION = 0.1
THIS_PROJ = hyperops
THIS_VERS = hyperops-$(VERSION)
THIS_SPKG = $(THIS_VERS).spkg
SAGE_ROOT = `sage -root`
SAGE_LOCAL = $(SAGE_ROOT)/local
CWD = "`pwd`"

all:
	@echo
	@echo "There is no 'all' target."
	@echo "Some targets you might find useful are:"
	@echo
	@echo "  clean     -- Removes any *.spkg, *.pyc, and *~ files."
	@echo "  copy      -- Makes a directory with a copy of important files."
	@echo "  spkg      -- Makes a Sage package suitable for 'sage -i *.spkg'."
	@echo "  install   -- Installs 'hyperops' in the site-packages directory."
	@echo "  uninstall -- Removes 'hyperops' from the site-packages directory."

clean:
	rm -rf $(THIS_VERS)
	find . -name '*~' | xargs rm -f
	find . -name '*.pyc' | xargs rm -f
	find . -name '*.spkg' | xargs rm -f

copy: clean
	mkdir $(THIS_VERS)
	for FILE in `find . -print | grep -v '.git' | grep './'` ; do \
	    if [ -d "$${FILE}" ] ; then mkdir -p "$(THIS_VERS)/$${FILE}" ; \
	    else cp "$${FILE}" "$(THIS_VERS)/$${FILE}" ; fi ; done
	rm -rf $(THIS_VERS)/$(THIS_VERS)

spkg: copy
	tar cvjf $(THIS_SPKG) $(THIS_VERS)
	rm -rf $(THIS_VERS)
	@echo
	@echo "The package '$(THIS_SPKG)' has been built."

check-root:
	if [ "$(SAGE_ROOT)" = "" ]; then \
	    echo "SAGE_ROOT undefined ... exiting" ; \
	    echo "Maybe run 'sage -sh'?" ; \
	    exit 1 ; fi

install: check-root copy
	cp -r $(CWD)/$(THIS_VERS) $(SAGE_LOCAL)/lib/python/site-packages/$(THIS_PROJ)

uninstall: check-root
	rm -rf $(SAGE_LOCAL)/lib/python/site-packages/$(THIS_PROJ)