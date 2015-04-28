<?xml version="1.0"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:exsl="http://exslt.org/common"
  extension-element-prefixes="exsl">

  <xsl:output
    method="html"
    encoding="utf-8"
    indent="no"
    doctype-system="about:legacy-compat"
    omit-xml-declaration="yes"
  />

  <!--copy all nodes and attributes...-->
  <xsl:template match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

  <!--add ../ to all a:hrefs-->
  <xsl:template mode="adjustpaths" match="a">
    <a>
      <xsl:attribute name="href">
        <xsl:value-of select="concat('../', @href)" />
      </xsl:attribute>
      <xsl:apply-templates mode="adjustpaths"
                           select="@*[name()!='href']|node()" />
    </a>
  </xsl:template>

  <xsl:template mode="adjustpaths" match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates mode="adjustpaths" select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

  <!--...but only within the body-->
  <xsl:template match="/">
    <html>
      <head>
        <xsl:copy-of select="document('inc-header.html')/head/*" />
        <title>Zélus Manual: <xsl:copy-of select="/html/head/title/text()"/></title>
        <meta name="description" content="Zélus user and reference manual."/>
        <meta name="author" content="Timothy Bourke and Marc Pouzet"/>
      </head>
      <body class="manual" data-spy="scroll" data-target=".sidebar-nav">
        <xsl:apply-templates mode="adjustpaths"
                             select="document('inc-titlebar.html')" />
        <script>
        window.onload = function() {
          document.getElementById('title-manual').className = 'active';
        };
        </script>
        <div class="container-fluid">
          <div class="row-fluid">
            <div class="span3 hidden-print">
              <div class="well sidebar-nav" data-spy="affix">
                <ul class="nav nav-list">
                  <xsl:apply-templates select="html/body" mode="navlinks"/>
                  <hr/>
                  <xsl:apply-templates select="html/body" mode="bodylinks"/>
                </ul>
              </div><!--/.well -->
            </div><!--/span-->
            <div class="span9 maintext">
              <xsl:apply-templates select="html/body"/>
            </div><!--/span-->
          </div><!--/row-->
        </div><!--/.fluid-container-->
        <xsl:copy-of select="document('inc-javascript.html')/contents/*" />
      </body>
    </html>
  </xsl:template>

  <!--extract the next, up, and previous buttons-->
  <xsl:template mode="navlinks" match="/html/body">
    <xsl:variable name="navlinks" select="a
      [descendant::img[@alt='Up' or @alt='Next' or @alt='Previous']]"/>
    <xsl:variable name="numnavlinks" select="count($navlinks) div 2"/>
    <xsl:for-each select="$navlinks">
      <xsl:if test="position() &lt;= $numnavlinks">
        <li><a href="{@href}"><xsl:value-of select="img/@alt"/></a></li>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <xsl:template mode="bodylinks" match="/html/body">
    <xsl:for-each select="h1 | h2 | h3">
      <li><a href="#{@id}">
          <xsl:value-of select="text()"/></a>
      </li>
    </xsl:for-each>
  </xsl:template>

  <!--
  <xsl:template match="h3">
    <xsl:variable name="header" select="."/>
    <div id="{concat(@id, '_link')}" class="example-section">
      <h3 id="{@id}" class="{@class}"><xsl:value-of select="text()"/></h3>
      <xsl:copy-of
        select="following-sibling::*[preceding-sibling::h3[1] = $header]"/>
    </div>
  </xsl:template>
  -->

  <!--strip away the <body> tags-->
  <xsl:template match="/html/body">
    <xsl:apply-templates/>
  </xsl:template>

  <!--strip away the first and last <hr>-->
  <xsl:template match="html/body/hr[position()=1 or last() and not(@class = 'footnoterule')]"/>

  <!--strip away the navigation links-->
  <xsl:template match="html/body/a
    [descendant::img[@alt='Up' or @alt='Next' or @alt='Previous']]"/>

</xsl:stylesheet>
