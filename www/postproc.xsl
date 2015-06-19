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

  <!--add srcset for retina displays-->
  <xsl:template match="img">
    <xsl:choose>
      <xsl:when test="'.png' =
        substring(@src, string-length(@src) - string-length('.png') + 1)">
        <img src="{@src}"
             srcset="{concat(substring-before(@src, '.png'), '@2x.png 2x')}" />
      </xsl:when>
      <xsl:otherwise>
        <img src="{@src}" srcset="{@srcset}" />
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

</xsl:stylesheet>
