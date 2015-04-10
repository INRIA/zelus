#!/bin/sh
#
#  The Zelus Hybrid Synchronous Language
#
#  Copyright (C) 2012-2013
#	Timothy Bourke
#	Marc Pouzet
#
#  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA
#
#   This file is distributed under the terms of the CeCILL-C licence
# 

##
# Configuration
SCRIPT=`basename $0`
SUFFIX=.rvrb

##
# Command-line

if [ $# -eq 0 ]; then
    INFILES=`ls *${SUFFIX}`
else
    for f in $@; do
      case $f in
      *${SUFFIX})
	INFILES="$INFILES $f"
	;;
      *)
	INFILES="$INFILES $f${SUFFIX}"
	;;
      esac
    done
fi

##
# Allocate temporary files

cleanup() {
    rm -f ${OUTFILE} ${ERRFILE}
}
OUTFILE=`mktemp -t ${SCRIPT}.out.XXXXXX` || exit 1
ERRFILE=`mktemp -t ${SCRIPT}.err.XXXXXX` || (cleanup; exit 1)
trap cleanup 1 2 15

##
# Code

#
# Given
#   var	    a variable to store the result
#   name    the filename prefix
#   num	    an id number
# generate a filename from name and num and store it in var.
#
setfilename() {
    local var="$1"
    local name="$2"
    local num="$3"
    if [ $num -lt 10 ]; then
	eval $var="${name}000${num}"
    elif [ $num -lt 100 ]; then
	eval $var="${name}00${num}"
    elif [ $num -lt 1000 ]; then
	eval $var="${name}0${num}"
    else
	eval $var="${name}${num}"
    fi
}

#
# If the WITHOPEN option is set, create a modified program text (with a
# different name) whose first lines import dependencies.
# Args:
#   filename	    the id of the program text
#   openfilenums    its dependencies (id list)
#
addopen() {
    local filename="$1"
    local openfilenums="$2"
    local of f
    if [ -n "$WITHOPEN" ]; then
	setfilename f "$PREFIX" $filename
	if [ -f "$SUBDIR$f$EXT" ]; then

	    local n openfiles=""
	    for n in $openfilenums; do
		setfilename of "$WITHOPEN" $n
		openfiles="$openfiles ${INCLUDECMD} $of"
	    done

	    setfilename of "$WITHOPEN" $filename
	    if [ -n "$openfiles" ]; then
		printf "$openfiles \n" > "$SUBDIR$of$EXT"
		cat $SUBDIR$f$EXT >> "$SUBDIR$of$EXT"
	    else
		cat $SUBDIR$f$EXT > "$SUBDIR$of$EXT"
	    fi
	fi
    fi
}

#
# Given
#   num		    a program (id)
#   openfilenums    its dependencies (id list)
# (Try to) Compile the program and create a corresponding .tex file that
# summarizes the results for reading back into the source document.
#
compile() {
    local num="$1"
    local openfilenums="$2"
    local ifile ofile outf
    local FILENAME

    # Decide whether to use the original program source or the version
    # augmented to import dependencies.
    if [ -n "$WITHOPEN" ]; then
	FILENAME=${WITHOPEN}
    else
	FILENAME=${PREFIX}
    fi

    # Generate the program (ifile) and output (ofile) filenames
    setfilename ifile "$FILENAME" $num
    ipath="$SUBDIR$ifile$EXT" 
    setfilename ofile "$PREFIX" $num
    opath="$SUBDIR$ofile.tex"

    # Check that the input file exists
    if [ -f "$ipath" ]; then
	printf "> $ofile$EXT...\n"
    else
	printf "> $ofile$EXT: program source not found.\n"
	return 1
    fi

    # Generate a list of dependency filenames to pass to the compiler
    local of n openfiles=""
    for n in $openfilenums; do
	setfilename of "$FILENAME" $n
	openfiles="$openfiles $SUBDIR$of$EXT"
    done

    # Invoke the compiler
    $COMPILER $COMPILERFLAGS $openfiles $LASTFLAGS "$ipath" >$OUTFILE 2>$ERRFILE
    COMPILERSTATUS=$?

    # Start the output tex file with the compilation command as a comment
    printf "%% $COMPILER $COMPILERFLAGS $openfiles \
	$LASTFLAGS $ipath ($COMPILERSTATUS)\n" > $opath

    # Signal compilation success (\runverbatimtrue) or not (\runverbatimfalse)
    if [ $COMPILERSTATUS -eq 0 ]; then
	printf '\\runverbatimtrue\n'   >> $opath
	if [ $shouldfail -eq 1 ]; then
	    printf "  unexpected success (line $linenum / page $pagenum)!\n" >&2
	fi
    else
	printf '\\runverbatimfalse\n'  >> $opath
	if [ $shouldfail -eq 0 ]; then
	    printf "  unexpected failure (line $linenum / page $pagenum)!\n" >&2
	    while read line
	    do
	      printf "  | $line\n"
	    done < $ERRFILE >&2
	fi
    fi

    # Include a sanitized compilation command (\setrunverbatimcmd)
    printf "\\\\setrunverbatimcmd{${COMPILERNAME} ${LASTFLAGS} \\\\runverbatimfile}\n" >> $opath

    # Include the compiler's stdout
    printf '\\begin{RunVerbatimMsg}\n' >> $opath
    if [ `wc -l < $OUTFILE` -eq 0 ]; then
	printf "Failed.\n"		  >> $opath
    else
	sed -e "s#$SUBDIR$ifile#$PREFIX#g" $OUTFILE >> $opath
    fi
    printf '\\end{RunVerbatimMsg}\n'   >> $opath

    # Include the compiler's stderr
    printf '\\begin{RunVerbatimErr}\n' >> $opath
    if [ `wc -l < $ERRFILE` -eq 0 ]; then
	printf "Success.\n"		  >> $opath
    else
	sed -e "s#$SUBDIR$ifile#$PREFIX#g" $ERRFILE >> $opath
    fi
    printf '\\end{RunVerbatimErr}\n'   >> $opath

    return 0
}

# Loop through each runverbatim command file
subdirs=
for infile in ${INFILES}; do

    # Add the suffix if necessary (as latex does)
    case $infile in
	*${SUFFIX}) ;;
	*) infile=${infile}${SUFFIX} ;;
    esac

    # Process each line of the command file
    while read l; do
	case $l in
	    subdir=*)
		SUBDIR=`expr "$l" : '.*=\(.*\)'`
		existing=`expr "$subdirs" : ".*:${SUBDIR}:\\([^:]*\\).*"`
		if [ -n "$existing" ]; then
		    printf "warning: %s: subdir=%s already used by %s!\n" \
			"$infile" "$SUBDIR" "$existing" >&2
		fi
		;;
	    prefix=*)
		PREFIX=`expr "$l" : '.*=\(.*\)'`
		;;
	    ext=*)
		EXT=`expr "$l" : '.*=\(.*\)'`
		;;
	    compiler=*)
		COMPILER=`expr "$l" : '.*=\(.*\)'`
		COMPILERNAME=`basename ${COMPILER}`
		;;
	    compilerflags=*)
		COMPILERFLAGS=`expr "$l" : '.*=\(.*\)'`
		;;
	    lastflags=*)
		LASTFLAGS=`expr "$l" : '.*=\(.*\)'`
		;;
	    includecmd=*)
		INCLUDECMD=`expr "$l" : '.*=\(.*\)'`
		if [ -z "$INCLUDECMD" ]; then
		    WITHOPEN=
		else
		    WITHOPEN=Withopen
		fi
		;;
	    *:*)
		# a snippet to be compiled
		filenum=`expr "$l" : '\(.*\):.*'`
		openfilenums=`expr "$l" : '.*:\(.*\)'`

		# build up a list of dependencies in opennums
		opennums=""
		for n in $openfilenums; do
		    case $n in
		    \[page=*\])
			pagenum=`expr "$n" : '\[page=\(.*\)\]'`
			;;
		    \[line=*\])
			linenum=`expr "$n" : '\[line=\(.*\)\]'`
			;;
		    \[fail\])
			shouldfail=1
			;;
		    *)
			if [ "$n" -eq "$n" ] 2>/dev/null; then
			    opennums="$opennums $n"
			else
			    printf "warning: $filenum: ignoring unresolved include '$n'\n" >&2
			fi
			;;
		    esac
		done

		addopen $filenum "$opennums"
		compile $filenum "$opennums"
		;;
	    *)
		printf "bad $infile: $l\n" >&2
		;;
	esac
	pagenum='?'
	linenum='?'
	shouldfail=0
    done < "${infile}"
    subdirs="${subdirs} :${SUBDIR}:${infile}:"
done

cleanup

