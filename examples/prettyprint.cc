// Copyright 2015 Kevin B. Hendricks, Stratford, Ontario,  All Rights Reserved.
// loosely based on a greatly simplified version of BeautifulSoup4 decode() routine
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Author: Kevin Hendricks
//
// Prettyprint back to html / xhtml

#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <string>
#include <unordered_set>

#include "gumbo.h"

static std::unordered_set<std::string> nonbreaking_inline  = { 
    "a","abbr","acronym","b","bdo","big","br","button","cite","code","del",
    "dfn","em","font","i","image","img","input","ins","kbd","label","map",
    "nobr","object","q","s","samp","select","small","span","strike","strong",
    "sub","sup","textarea","tt","u","var","wbr"
};


static std::unordered_set<std::string> preserve_whitespace = {
    "pre","textarea","script","style"
};


static std::unordered_set<std::string> special_handling    = { 
    "html","body"
};


static std::unordered_set<std::string> no_entity_sub       = {
    "script","style"
};


static std::unordered_set<std::string> empty_tags          = {
    "area","base","basefont","bgsound","br","command","col","embed",
    "event-source","frame","hr","image","img","input","keygen","link",
    "menuitem","meta","param","source","spacer","track","wbr"
};


static std::unordered_set<std::string> structural_tags     = {
    "article","aside","blockquote","body","canvas","div","dl","figure",
    "footer","head","header","hr","html","ol","section","script","style",
    "table","ul"
};


static inline bool in_set(std::unordered_set<std::string> &s, std::string &key)
{
  return s.find(key) != s.end();
}

// These need to match the GumboAttributeNamespaceEnum sequence
static const char * attribute_nsprefixes[4] = { "", "xlink:", "xml:", "xmlns:" };


static inline void rtrim(std::string &s) 
{
  s.erase(s.find_last_not_of(" \n\r\t\v\f")+1);
}


static inline void ltrim(std::string &s)
{
  s.erase(0,s.find_first_not_of(" \n\r\t\v\f"));
}


static inline void ltrimnewlines(std::string &s)
{
  s.erase(0,s.find_first_not_of("\n\r"));
}


// erase everything up to and including the newline
static void newlinetrim(std::string &s)
{
  size_t pos = s.find("\n");
  if (pos != std::string::npos) {
    s.erase(0, pos+1);
  }
}


static void replace_all(std::string &s, const char * s1, const char * s2)
{
  std::string t1(s1);
  size_t len = t1.length();
  size_t pos = s.find(t1);
  while (pos != std::string::npos) {
    s.replace(pos, len, s2);
    pos = s.find(t1, pos + len);
  }
}


static std::string substitute_xml_entities_into_text(const std::string &text)
{
  std::string result = text;
  // replacing & must come first 
  replace_all(result, "&", "&amp;");
  replace_all(result, "<", "&lt;");
  replace_all(result, ">", "&gt;");
  return result;
}


static std::string substitute_xml_entities_into_attributes(char quote, const std::string &text)
{
  std::string result = substitute_xml_entities_into_text(text);
  if (quote == '"') {
    replace_all(result,"\"","&quot;");
  }    
  else if (quote == '\'') {
    replace_all(result,"'","&apos;");
  }
 return result;
}


static std::string get_tag_name(GumboNode *node)
{
  std::string tagname;
  if (node->type == GUMBO_NODE_DOCUMENT) {
    tagname = "#document";
    return tagname;
  } else if ((node->type == GUMBO_NODE_TEXT) || (node->type == GUMBO_NODE_WHITESPACE)) {
    tagname = "#text";
    return tagname;
  } else if (node->type == GUMBO_NODE_CDATA) {
    tagname = "#cdata";
    return tagname;
  }
  tagname = gumbo_normalized_tagname(node->v.element.tag);
  if ((tagname.empty()) ||
      (node->v.element.tag_namespace == GUMBO_NAMESPACE_SVG)) {

    // set up to examine original text of tag.
    GumboStringPiece gsp = node->v.element.original_tag;
    gumbo_tag_from_original_text(&gsp);

    // special handling for some svg tag names.
    if (node->v.element.tag_namespace  == GUMBO_NAMESPACE_SVG) {
      const char * data = gumbo_normalize_svg_tagname(&gsp);
      // NOTE: data may not be null-terminated!
      // since case change only - length must be same as original.
      // if no replacement found returns null, not original tag!
      if (data != NULL) {
        return std::string(data, gsp.length);
      }
    }
    if (tagname.empty()) {
      return std::string(gsp.data, gsp.length);
    }
  }
  return tagname;
}


static std::string build_doctype(GumboNode *node)
{
  std::string results = "";
  if (node->v.document.has_doctype) {
    results.append("<!DOCTYPE ");
    results.append(node->v.document.name);
    std::string pi(node->v.document.public_identifier);
    if ((node->v.document.public_identifier != NULL) && !pi.empty() ) {
        results.append(" PUBLIC \"");
        results.append(node->v.document.public_identifier);
        results.append("\"\n    \"");
        results.append(node->v.document.system_identifier);
        results.append("\"");
    }
    results.append(">\n");
  }
  return results;
}


// handle the known foreign attribute namespaces
static std::string get_attribute_name(GumboAttribute * at)
{
  std::string attr_name = at->name;
  GumboAttributeNamespaceEnum attr_ns = at->attr_namespace;
  if ((attr_ns == GUMBO_ATTR_NAMESPACE_NONE) || (attr_name == "xmlns")) {
    return attr_name;
  } 
  attr_name = std::string(attribute_nsprefixes[attr_ns]) + attr_name;
  return attr_name;
}


static std::string build_attributes(GumboAttribute * at, bool no_entities)
{
  std::string atts = " ";
  std::string name = get_attribute_name(at);
  atts.append(name);
  std::string attvalue = at->value;

  // we handle empty attribute values like so: alt=""
  char quote = '"';
  std::string qs="\"";

  if ( (!attvalue.empty())   || 
       (at->original_value.data[0] == '"') || 
       (at->original_value.data[0] == '\'') ) {

    // determine original quote character used if it exists
    quote = at->original_value.data[0];
    if (quote == '\'') qs = std::string("'");
    if (quote == '"') qs = std::string("\"");
  }

  atts.append("=");
  atts.append(qs);
  if (no_entities) {
    atts.append(attvalue);
  } else {
    atts.append(substitute_xml_entities_into_attributes(quote, attvalue));
  }
  atts.append(qs);
  return atts;
}

// forward declaration

static std::string prettyprint(GumboNode*, int lvl, const std::string indent_chars);


static std::string prettyprint_contents(GumboNode* node, int lvl, const std::string indent_chars) 
{
  std::string contents        = "";
  std::string tagname         = get_tag_name(node);
  bool no_entity_substitution = in_set(no_entity_sub, tagname);
  bool keep_whitespace        = in_set(preserve_whitespace, tagname);
  bool is_inline              = in_set(nonbreaking_inline, tagname);
  bool is_structural          = in_set(structural_tags, tagname);
  bool pp_okay                = !is_inline && !keep_whitespace;
  char c                      = indent_chars.at(0);
  int  n                      = indent_chars.length(); 

  GumboVector* children = &node->v.element.children;

  for (unsigned int i = 0; i < children->length; ++i) {

    GumboNode* child = static_cast<GumboNode*> (children->data[i]);

    if (child->type == GUMBO_NODE_TEXT) {
      std::string val;

      if (no_entity_substitution) {
        val = std::string(child->v.text.text);
      } else {
        val = substitute_xml_entities_into_text(std::string(child->v.text.text));
      }

      // if first child of a structual element is text, indent it properly
      if ((i==0) && is_structural) {
        std::string indent_space = std::string((lvl-1)*n,c);
        contents.append(indent_space);
        ltrim(val);
      }
      contents.append(val);

    } else if (child->type == GUMBO_NODE_ELEMENT || child->type == GUMBO_NODE_TEMPLATE) {

      std::string val = prettyprint(child, lvl, indent_chars);
      contents.append(val);

    } else if (child->type == GUMBO_NODE_WHITESPACE) {

      if (keep_whitespace || is_inline) {
        std::string wspace = std::string(child->v.text.text);
        contents.append(wspace);
      }

    } else if (child->type == GUMBO_NODE_CDATA) {
      contents.append("<![CDATA[" + std::string(child->v.text.text) + "]]>");

    } else if (child->type == GUMBO_NODE_COMMENT) {
      contents.append("<!--" + std::string(child->v.text.text) + "-->");
 
    } else {
      fprintf(stderr, "unknown element of type: %d\n", child->type); 
    }

  }

  return contents;
}


// prettyprint a GumboNode back to html/xhtml
// may be invoked recursively

static std::string prettyprint(GumboNode* node, int lvl, const std::string indent_chars)
{

  // special case the document node
  if (node->type == GUMBO_NODE_DOCUMENT) {
    std::string results = build_doctype(node);
    results.append(prettyprint_contents(node,lvl+1,indent_chars));
    return results;
  }

  std::string close              = "";
  std::string closeTag           = "";
  std::string atts               = "";
  std::string tagname            = get_tag_name(node);
  std::string parentname         = get_tag_name(node->parent);

  bool in_head                   = (parentname == "head");
  bool need_special_handling     = in_set(special_handling, tagname);
  bool is_empty_tag              = in_set(empty_tags, tagname);
  bool no_entity_substitution    = in_set(no_entity_sub, tagname);
  bool keep_whitespace           = in_set(preserve_whitespace, tagname);
  bool is_inline                 = in_set(nonbreaking_inline, tagname) && !in_set(structural_tags, parentname);
  bool is_structural             = in_set(structural_tags, tagname);
  bool pp_okay                   = !is_inline && !keep_whitespace;
  char c                         = indent_chars.at(0);
  int  n                         = indent_chars.length(); 

  // build attr string
  const GumboVector * attribs = &node->v.element.attributes;
  for (int i=0; i< attribs->length; ++i) {
    GumboAttribute* at = static_cast<GumboAttribute*>(attribs->data[i]);
    atts.append(build_attributes(at, no_entity_substitution));
  }

  // determine closing tag type
  if (is_empty_tag) {
    close = "/";
  } else {
    closeTag = "</" + tagname + ">";
  }

  std::string indent_space = std::string((lvl-1)*n,c);
  std::string contents;

  // prettyprint your contents
  if (is_structural && tagname != "html") {
    contents = prettyprint_contents(node, lvl+1, indent_chars);
  } else {
    contents = prettyprint_contents(node, lvl, indent_chars);
  }

  if (is_structural) {
    rtrim(contents);
    if (!contents.empty()) contents.append("\n");
  }

  char last_char = ' ';
  if (!contents.empty()) {
    last_char = contents.at(contents.length()-1);
  } 

  // build results
  std::string results;

  if (!is_inline) {
    results.append(indent_space);
  }

  results.append("<"+tagname+atts+close+">");

  if (pp_okay && is_structural && !contents.empty()) {
    results.append("\n");
  }

  results.append(contents);

  if (pp_okay && (last_char != '\n') && !contents.empty() && is_structural) {
    results.append("\n");
  }

  // handle any indent before structural close tags
  if (!is_inline && is_structural && !closeTag.empty() && !contents.empty()) {
    results.append(indent_space);
  }

  results.append(closeTag);

  if (pp_okay) {
    results.append("\n");
  }

  return results;
}



int main(int argc, char** argv) {
  if (argc != 2) {
      std::cout << "prettyprint <html filename>\n";
      exit(EXIT_FAILURE);
  }
  const char* filename = argv[1];

  std::ifstream in(filename, std::ios::in | std::ios::binary);
  if (!in) {
    std::cout << "File " << filename << " not found!\n";
    exit(EXIT_FAILURE);
  }

  std::string contents;
  in.seekg(0, std::ios::end);
  contents.resize(in.tellg());
  in.seekg(0, std::ios::beg);
  in.read(&contents[0], contents.size());
  in.close();
 
  GumboOptions myoptions = kGumboDefaultOptions;
  myoptions.use_xhtml_rules = true;

  GumboOutput* output = gumbo_parse_with_options(&myoptions, contents.data(), contents.length());
  std::string indent_chars = "  ";
  std::cout << prettyprint(output->document, 0, indent_chars) << std::endl;
  gumbo_destroy_output(output);
}
