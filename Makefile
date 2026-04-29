all:
	cd src && $(MAKE)

install: all
	cd src && $(MAKE) install

clean: 
	git clean -fdx
