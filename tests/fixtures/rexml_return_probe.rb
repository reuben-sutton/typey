# typed: true

require "rexml/document"

module REXML
  class Document; end
  class Element; end
  class CData; end
end

document = REXML::Document.new
element = REXML::Element.new("test")
cdata = REXML::CData.new("body")

T.reveal_type(element.add_attributes("name" => "value")) # note: T::Hash[String, String]
T.reveal_type(element.add_element("child")) # note: REXML::Element
T.reveal_type(element.add(cdata)) # note: REXML::CData
T.reveal_type(document << cdata) # note: REXML::CData
T.reveal_type(document.add_element(element)) # note: REXML::Element
