#!/bin/sh

########################################################################
#
# How does it work?
#
# 1. Create a file called "readme.md" in each examples/* directory that
#    should be included on the website. These files are in "markdown" format
#    with special directives for including source files (see below).
#
# 2. Any images (*.png, *.jpg) in an examples/*/img directory will also be
#    copied to the website.
#
# 3. Optionally adjust the configuration parameters below.
#
# 4. Run the script to generate updated pages.
#
# Are there any special dependencies?
#
# Yes, you will need:
#
# 1. A standard Unix environment (sh, cat, rm, find, mkdir, etc.)
#
# 2. A script for turning markdown into html, see:
#	http://daringfireball.net/projects/markdown/
#
# 3. A script for turning bibtex into html, see:
#	https://www.lri.fr/~filliatr/bibtex2html/
#

# Location of Zélus source
ZELUS=..

# Location to store generated html files
WWW=./www

# Path to the markdown script (http://daringfireball.net/projects/markdown/)
MARKDOWN=multimarkdown

# Path to bibtex2html (https://www.lri.fr/~filliatr/bibtex2html)
BIBTEX2HTML=bibtex2html

##

SOURCES="src/index.html
	 src/examples.html
	 src/download.html
	 src/contact.html
	 src/papers.html"

GENERATED=./generated
EXAMPLES="${ZELUS}/examples/bouncingball
	  ${ZELUS}/examples/bangbang
	  ${ZELUS}/examples/soas_relaycontrol
	  ${ZELUS}/examples/stickysprings
	  ${ZELUS}/examples/backhoe
	  ${ZELUS}/examples/airtraffic"
TOOLS=${ZELUS}/tools

ORIG_IFS=$IFS

########################################################################
# Check paramters

if [ ! `which ${MARKDOWN}` ]; then
    if [ `which multimarkdown` ]; then
	MARKDOWN=multimarkdown
	printf "info: using ${MARKDOWN}.\n"\n 1>&2
    else
	printf "warning: ${MARKDOWN} not found.\n" 1>&2
	MARKDOWN=cat
    fi
fi

########################################################################
#
# Turn each readme.md entry in EXAMPLES into html.
#
# The readme.md files may mix html and markdown:
#   http://daringfireball.net/projects/markdown/
#
# Each should being with a title line like:
#   ## Name of example ##
# (The "##"s mark it as a heading (<h2>).)
#
# They may also contain special directives (each on its own line):
#   !REQUIRES: <list of required libraries>
#   !SOURCEFILE: <Zélus source file to include>
#

mkdir -p ${GENERATED}
rm -f ${GENERATED}/gen-examples-body.html \
      ${GENERATED}/gen-examples-nav-local.html \
      ${GENERATED}/gen-examples-nav-other.html

for ENTRY in ${EXAMPLES}; do
    EX=${ENTRY}/readme.md
    EXDIR=`dirname ${EX}`
    EXNAME=`basename ${EXDIR}`
    TITLE=`sed -n "s/##* \([^#]*\) ##*/\1/p;q" "${EX}"`

    printf "<div id=\"${EXNAME}\" class=\"example-section\">\n" \
	>> "${GENERATED}/gen-examples-body.html"
    IFS="
"
    (cat ${EX} | ${MARKDOWN} | while read LINE
    do
	case "${LINE}" in
	    *!SOURCEFILE:*ls*)
		FILE=`expr "$LINE" : '.*!SOURCEFILE: *\([^ ]*\).zls'`
		cat <<EOF
<div id="${EXNAME}-${FILE}-box" class="accordion sourcefile">
<div class="accordion-group">
<div class="accordion-heading">
<a class="accordion-toggle" data-toggle="collapse"
   data-parent="#${EXNAME}-${FILE}-box"
   href="#${EXNAME}-${FILE}"><i class="icon-file"></i> ${FILE}.zls</a>
</div>

<div id="${EXNAME}-${FILE}" class="accordion-body">
<div class="accordion-inner">
EOF
		${TOOLS}/zltohtml ${EXDIR}/${FILE}.zls
		printf "</div></div></div></div>\n"
		;;
	    *!REQUIRES:*)
		printf '<div class="requirements">\n'
		printf '<p class="text-info">\n'
		printf '<i class="icon-info-sign"></i> <em>Requires</em>:\n'
		printf `expr "$LINE" : '.*!REQUIRES: *\(.*\)'`
		printf '\n</p>\n'
		printf '</div>\n'
		;;
	    *)
		printf "$LINE\n"
		;;
	esac
    done >> "${GENERATED}/gen-examples-body.html")
    IFS=$ORIG_IFS
    printf "</div><hr />\n" >> "${GENERATED}/gen-examples-body.html"

    printf "<li><a href=\"#${EXNAME}\">${TITLE}</a></li>\n" \
	>> "${GENERATED}/gen-examples-nav-local.html"
    printf "<li><a href=\"examples.html#${EXNAME}\">${TITLE}</a></li>\n" \
	>> "${GENERATED}/gen-examples-nav-other.html"

    # copy image files
    mkdir -p ${WWW}/img
    if [ -d "${EXDIR}/img" ]; then
	for f in ${EXDIR}/img/*.png ${EXDIR}/img/*.jpg
	do
	    [ -f "$f" ] || continue
	    cp $f ${WWW}/img/`basename $f`
	    printf "added: ${WWW}/img/`basename $f`\n"
	done
    fi
done

########################################################################
#
# Produce the bibliographies (one for each *.bib file in src)
#

if [ ! `which ${BIBTEX2HTML}` ]; then
    printf "warning: ${BIBTEX2HTML} not found.\n" 1>&2
    BIBTEX2HTML=cat
fi

rm -f ${GENERATED}/gen-bib-nav-local.html
for BIB in src/*.bib; do
    BASENAME=`basename ${BIB}`
    NAME=`expr "${BASENAME}" : '\(.*\).bib'`
    (cd "${GENERATED}";
     ${BIBTEX2HTML} -q -d -r -nodoc -unicode -linebreak \
 	-noheader -nofooter -nobiblinks -s alpha \
	-o "${NAME}" -dl "../${BIB}")

    sed -e 's/<font [^>]*>//' \
	-e 's/<\/font>//' \
	-e 's/<p>/<\/p><p>/' \
	-e 's/<blockquote>/<div class="abstract"><p>/' \
	-e 's/<\/blockquote>/<\/p><\/div>/' \
	-e 's/^<\/p><p>//' \
	-e 's/\[<a name="\([^0-9]*\)\([0-9]*\)">[^<]*<\/a>\]/<a id="\1\2" class="biblink" name="\1\2">\1 \2<\/a>/' \
	-e 's/.*<a href="\([^"]*\)">DOI<\/a>.*/<span class="bibref"><a href="\1"><i class="icon-globe"><\/i> DOI<\/a><\/span>/' \
	-e 's/.*<a href="\([^"]*\)">.pdf<\/a>.*/<span class="bibref"><a href="\1"><i class="icon-file"><\/i> pdf<\/a><\/span>/' \
	-e 's/.*<a href="\([^"]*\)">bib<\/a>.*/<span class="bibref"><a href="\1"><i class="icon-book"><\/i> bib<\/a><\/span>/' \
	"${GENERATED}/${NAME}.html" \
	> "${GENERATED}/${NAME}-post.html"
    mv "${GENERATED}/${NAME}-post.html" "${GENERATED}/${NAME}.html"

    grep '<a id="[^>]*".*' "${GENERATED}/${NAME}.html" | while read line
    do
	BIBKEY=`expr "${line}" : '<a id="\([^"]*\)" class="[^"]*" name="[^"]*">[^<]*</a>'`
	BIBNAME=`expr "${line}" : '<a id="[^"]*" class="[^"]*" name="[^"]*">\([^<]*\)</a>'`
	printf "<li><a href=\"#${BIBKEY}\">${BIBNAME}</a></li>\n" \
	    >> ${GENERATED}/gen-bib-nav-local.html
    done


    printf "added: ${WWW}/${NAME}_bib.html\n"
    cp "${GENERATED}/${NAME}_bib.html" "${WWW}/"
done

########################################################################
#
# Process each of the files from SOURCES into WWW, replacing:
#
# !INCLUDE: <path>	    with the contents of <path>
#

mkdir -p ${WWW}
for SRC in ${SOURCES}; do
    DST=${WWW}/`basename ${SRC}`
    rm -f "${DST}"

    (cat "${SRC}" | while read LINE
    do
	case "${LINE}" in
	    *!INCLUDE:*)
		IFILE=`expr "$LINE" : '.*!INCLUDE: *\([^ ]*\)'`
		cat "${IFILE}"
		;;
	    *)
		printf "${LINE}\n"
		;;
	esac
    done) >> ${DST}
    printf "added: ${DST}\n"
done

