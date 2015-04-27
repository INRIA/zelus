<?xml version="1.0"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:exsl="http://exslt.org/common"
  extension-element-prefixes="exsl"
  xmlns:xi="http://www.w3.org/2001/XInclude">

  <xsl:output
    method="xml"
    encoding="utf-8"
    indent="no"
    omit-xml-declaration="yes"
  />

  <!--copy all nodes and attributes...-->
  <xsl:template match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

  <!--...but only within the body-->
  <xsl:template match="/">
    <html>
      <head>
        <xi:include href="inc-header.xml"/>
        <title>Zélus Manual: <xsl:copy-of select="/html/head/title/text()"/></title>
        <meta name="description" content="Zélus user and reference manual."/>
        <meta name="author" content="Timothy Bourke and Marc Pouzet"/>
      </head>
      <body>
        <xsl:apply-templates select="html/body"/>
      </body>
    </html>
  </xsl:template>

  <!--strip away the <body> tags-->
  <xsl:template match="/html/body">
    <exsl:document
      href="./blah.txt"
      method="xml"
      encoding="utf-8"
      omit-xml-declaration="yes">
        <!--extract the next, up, and previous buttons-->
        <xsl:variable name="navlinks" select="a
          [descendant::img[@alt='Up' or @alt='Next' or @alt='Previous']]"/>
        <xsl:variable name="numnavlinks" select="count($navlinks) div 2"/>
        <xsl:for-each select="$navlinks">
          <xsl:if test="position() &lt;= $numnavlinks">
            <li><a href="{@href}"><xsl:value-of select="img/@alt"/></a></li>
            <xsl:text>&#xa;</xsl:text>
          </xsl:if>
        </xsl:for-each>
        <hr/>
        <!--make links to the <h3> tags-->
        <xsl:text>&#xa;</xsl:text>
        <xsl:for-each select="h3">
            <li><a href="#{@id}"><xsl:value-of select="text()"/></a></li>
            <xsl:text>&#xa;</xsl:text>
        </xsl:for-each>
    </exsl:document>
    <xsl:apply-templates/>
  </xsl:template>

  <!--write the title out to a file-->
  <xsl:template match="/html/head/title">
    <exsl:document
      href="./title.txt"
      method="text"
      encoding="utf-8">
      <xsl:value-of select="text()"/>
    </exsl:document>
  </xsl:template>

  <!--strip away the first and last <hr>-->
  <xsl:template match="html/body/hr[position()=1 or last()]"/>

  <!--strip away the navigation links-->
  <xsl:template match="html/body/a
    [descendant::img[@alt='Up' or @alt='Next' or @alt='Previous']]"/>

</xsl:stylesheet>
