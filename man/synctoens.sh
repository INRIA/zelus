#!/bin/sh

# Location where generated html files are stored
WWW=./wwwman

# Server details
USER=${1:-"zelus"}
SERVER=di.ens.fr
SERVERWWW=~zelus/public_html

rsync -avz -e ssh --omit-dir-times --exclude .svn "${WWW}/" \
    ${USER}@${SERVER}:"${SERVERWWW}/man"

