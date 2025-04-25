// Script to mark adjacent links so that these can be styled with a dotted underline

document.addEventListener('DOMContentLoaded', function () {
  // Function to process all content areas
  function markAdjacentLinks() {
    // Target content areas
    const contentElements = document.querySelectorAll('.content');

    contentElements.forEach((content) => {
      // Get all links in the content area
      const links = content.querySelectorAll('a');

      for (let i = 0; i < links.length; i++) {
        // Skip links in excluded contexts (pre, code, etc.)
        if (isExcludedContext(links[i])) continue;

        // Check if current link is followed by another
        if (i < links.length - 1) {
          const currentLink = links[i];
          const nextLink = links[i + 1];

          // Skip excluded contexts for next link too
          if (isExcludedContext(nextLink)) continue;

          // Check if there's no text between the links
          if (areDirectlyAdjacent(currentLink, nextLink)) {
            currentLink.classList.add('adjacent-link');
            nextLink.classList.add('adjacent-link');
          }
        }
      }
    });
  }

  // Check if a link is in a context we want to exclude (pre, code, etc.)
  function isExcludedContext(link) {
    return (
      link.closest('pre') ||
      link.closest('code') ||
      link.closest('.Agda') ||
      link.classList.contains('concept')
    );
  }

  // Check if two links are directly adjacent with no text between
  function areDirectlyAdjacent(link1, link2) {
    // Start with the node right after link1
    let node = link1.nextSibling;

    // Check all nodes between link1 and link2
    while (node && node !== link2) {
      // If there's any non-whitespace text content between, the links are not adjacent
      if (node.nodeType === Node.TEXT_NODE && node.textContent.trim() !== '') {
        return false;
      }

      // If there's another element that's not link2, links are not adjacent
      if (node.nodeType === Node.ELEMENT_NODE && node !== link2) {
        return false;
      }

      node = node.nextSibling;
    }

    // If we reached link2 without finding text or other elements, links are adjacent
    return node === link2;
  }

  // Run the function
  markAdjacentLinks();

  // Re-run when content might change (e.g., after page navigation in SPAs)
  document.addEventListener('mdbook-content-loaded', markAdjacentLinks);
});
