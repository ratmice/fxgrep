##############################################################################
# This specifies what must be installed. 
# fxgrep is the querying program. 
# fxgreplib is the library (must be installed for fxt)
##############################################################################
TO_INSTALL = fxgrep fxgreplib

##############################################################################
# These are the locations for executables, heap images and library files
##############################################################################
PREFIX        = /home/psi/aberlea/install
FXP_LIBDIR    = ${PREFIX}/fxp
FXGREP_BINDIR = ${PREFIX}/bin
FXGREP_LIBDIR = ${PREFIX}/fxgrep

##############################################################################
# The path where the SML-NJ binaries are located, and the name of the 
# SML-NJ executable with the Compilation manager built-in. If sml is in 
# your PATH at execution time, you fon't need the full path here.  
##############################################################################
SML_BINDIR = /local/sml/bin
SML_EXEC   = ${SML_BINDIR}/sml
##############################################################################
# No need to change this for SML-NJ 110.0.6. For earlier or working versions  
# 110.19 you might have to use the second or third line. This is the
# compilation manager function for making with a named description file. 
##############################################################################
SML_MAKEDEF= val make = CM.make'
#SML_MAKEDEF= val make = CM.make
#SML_MAKEDEF= fun make x = CM.make'{force_relink=true, group=x}

##############################################################################
# These should be fine on most unix machines
##############################################################################
SED       = sed
RM        = rm -f
RMDIR     = rmdir
COPY      = cp -f
CHMOD     = chmod
FIND      = find
MKDIRHIER = mkdirhier

##############################################################################
# nothing to change below this line
##############################################################################
SRC         = src
FXGREPLIB_PRUNE = \( -path '*/CM*' -o -path '*/CVS*' -o -path '*.y.sml' \)

all:
	for prog in ${TO_INSTALL}; do \
	    make image.$${prog}; \
	done

arch.os:
	${SML_BINDIR}/.arch-n-opsys | \
	${SED} -e 's/^.*HEAP_SUFFIX=\(.*\)$$/\1/' > .arch-opsys

fxlib.cm: Makefile 
	echo Alias ${FXP_LIBDIR}/fxlib.cm > ${SRC}/fxlib.cm


fxgrep.sh: Makefile arch.os
	${RM} fxgrep.sh
	echo "#!/bin/sh -f" > fxgrep.sh
	echo >> fxgrep.sh
	echo "SML_BINDIR=${SML_BINDIR}" >> fxgrep.sh
	echo "FXGREP_LIBDIR=${FXGREP_LIBDIR}" >> fxgrep.sh
	cat fxgrep.sh.in >> fxgrep.sh

image.fxgreplib:

image.fxgrep: fxlib.cm
	@echo "Creating the ${PROG_NAME} heap image..."
	echo "${SML_MAKEDEF}; make \"${SRC}/fxgrep.cm\"; \
	      SMLofNJ.exportFn(\"${SRC}/_fxgrep\",Grep.grep)" | ${SML_EXEC}


inst.dirs:
	test -d ${FXGREP_BINDIR} || ${MKDIRHIER} ${FXGREP_BINDIR}	
	test -d ${FXGREP_LIBDIR} || ${MKDIRHIER} ${FXGREP_LIBDIR}

inst.fxgreplib: inst.dirs fxlib.cm
	for dir in `${FIND} ${SRC} ${FXGREPLIB_PRUNE} -prune -o -type d -print`; do \
	    ${MKDIRHIER} ${FXGREP_LIBDIR}/$${dir}; \
	done;
	for file in `${FIND} ${SRC} ${FXGREPLIB_PRUNE} -prune -o -name "*.cm" -print -o -name "*.y" -print -o -name "*.sml"  -print -o -name "*.sig" -print`; do \
	    ${COPY} $${file} ${FXGREP_LIBDIR}/$${file}; \
	done
	rm -f ${FXGREP_LIBDIR}/fxgrep.cm
	echo Group is > ${FXGREP_LIBDIR}/fxgrep.cm
	echo "  "${SRC}/fxgrep.cm >> ${FXGREP_LIBDIR}/fxgrep.cm


inst.fxgrep:  inst.dirs fxgrep.sh arch.os
	${RM} ${FXGREP_BINDIR}/fxgrep ${FXGREP_BINDIR}/fxgrep.sh \
	      ${FXGREP_LIBDIR}/_fxgrep.`cat .arch-opsys`
	${COPY} fxgrep.sh ${FXGREP_BINDIR}/fxgrep
	${CHMOD} 755 ${FXGREP_BINDIR}/fxgrep
	${COPY} ${SRC}/_fxgrep.`cat .arch-opsys` ${FXGREP_LIBDIR}
	${CHMOD} 644 ${FXGREP_LIBDIR}/_fxgrep.`cat .arch-opsys`


install:
	for prog in ${TO_INSTALL}; do \
	    make inst.$${prog}; \
	done

clean:
	-${RM} -f ${SRC}/_fx.* fxgrep.sh .arch-opsys ${SRC}/fxlib.cm
	-find ${SRC} -type d -name CM -print | xargs ${RM} -r 
