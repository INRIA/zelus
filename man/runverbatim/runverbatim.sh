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

#
# TODO: incorporate support for executing generated files:
#	- include their output
#	- and/or generate graphs of their runs
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
    INFILES=$@
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
		echo "$openfiles" > "$SUBDIR$of$EXT"
		cat $SUBDIR$f$EXT >> "$SUBDIR$of$EXT"
	    else
		cat $SUBDIR$f$EXT > "$SUBDIR$of$EXT"
	    fi
	fi
    fi
}

compile() {
    local num="$1"
    local openfilenums="$2"
    local file ofile outf
    local FILENAME

    if [ -n "$WITHOPEN" ]; then
	FILENAME=${WITHOPEN}
    else
	FILENAME=${PREFIX}
    fi

    setfilename file "$FILENAME" $num
    setfilename ofile "$PREFIX" $num

    if [ -f "$SUBDIR$file$EXT" ]; then
	echo "> $ofile$EXT..."
    else
	echo "> $ofile$EXT: not found."
	return 1
    fi

    local of n openfiles=""
    for n in $openfilenums; do
	setfilename of "$FILENAME" $n
	openfiles="$openfiles $SUBDIR$of$EXT"
    done

    outf="$SUBDIR$ofile.tex"

    $COMPILER $COMPILERFLAGS $openfiles \
	$LASTFLAGS $SUBDIR$file$EXT >$OUTFILE 2>$ERRFILE
    COMPILERSTATUS=$?

    echo "% $COMPILER $COMPILERFLAGS $openfiles \
	$LASTFLAGS $SUBDIR$file$EXT ($COMPILERSTATUS)" > $outf
    if [ $COMPILERSTATUS -eq 0 ]; then
	echo '\\runverbatimtrue'   >> $outf
	if [ $shouldfail -eq 1 ]; then
	    echo "  unexpected success (line $linenum / page $pagenum)!" >&2
	fi
    else
	echo '\\runverbatimfalse'  >> $outf
	if [ $shouldfail -eq 0 ]; then
	    echo "  unexpected failure (line $linenum / page $pagenum)!" >&2
	fi
    fi

    echo "\\\\setrunverbatimcmd{${COMPILERNAME} ${LASTFLAGS} \\\\runverbatimfile}" >> $outf

    echo '\\begin{RunVerbatimMsg}' >> $outf
    if [ `wc -l < $OUTFILE` -eq 0 ]; then
	echo "Failed."		  >> $outf
    else
	sed -e "s#$SUBDIR$file#$PREFIX#g" $OUTFILE >> $outf
    fi
    echo '\\end{RunVerbatimMsg}'   >> $outf

    echo '\\begin{RunVerbatimErr}' >> $outf
    if [ `wc -l < $ERRFILE` -eq 0 ]; then
	echo "Success."		  >> $outf
    else
	sed -e "s#$SUBDIR$file#$PREFIX#g" $ERRFILE >> $outf
    fi
    echo '\\end{RunVerbatimErr}'   >> $outf

    return 0
}

for infile in ${INFILES}; do
    case $infile in
	*${SUFFIX}) ;;
	*) infile=${infile}${SUFFIX} ;;
    esac

    while read l; do
	case $l in
	    subdir=*)
		SUBDIR=`expr "$l" : '.*=\(.*\)'`
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
		filenum=`expr "$l" : '\(.*\):.*'`
		openfilenums=`expr "$l" : '.*:\(.*\)'`

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
			    echo "warning: $filenum: ignoring unresolved include '$n'" >&2
			fi
			;;
		    esac
		done

		addopen $filenum "$opennums"
		compile $filenum "$opennums"
		;;
	    *)
		echo "bad $infile: $l" >&2
		;;
	esac
	pagenum='?'
	linenum='?'
	shouldfail=0
    done < "${infile}"
done

cleanup

