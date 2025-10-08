// This script generates the GitHub link for the edit button on each page of the website
const link = document.querySelector('.href-git-edit-button');
if (link) {
  // console.log(link);
  var filename = link.getAttribute('href');
  const excludeList = [
    'SUMMARY.md',
  ];
  const rootFileList = [
    'CONTRIBUTING.md',
    'LICENSE.md',
    'README.md',
  ];
  const docsFileList = [
    'ART.md',
    'CITE-THIS-LIBRARY.md',
    'CITING-SOURCES.md',
    'CODINGSTYLE.md',
    'DESIGN-PRINCIPLES.md',
    'FILE-CONVENTIONS.md',
    'GRANT-ACKNOWLEDGMENTS.md',
    'HOME.md',
    'HOWTO-INSTALL.md',
    'MIXFIX-OPERATORS.md',
    'PROJECTS.md',
    'STATEMENT-OF-INCLUSIVITY.md',
    'TEMPLATE.lagda.md',
    'VISUALIZATION.md',
  ];

  if (excludeList.includes(filename)) {
    // Default to the main GitHub page for excluded pages
    link.setAttribute('href', 'https://github.com/UniMath/agda-unimath');
  }
  else {
    // Generate the correct file path on the repo side
    var path = '';
    if (filename === 'index.md') {
      path = 'docs/HOME.md';
    } else if (filename === 'CONTRIBUTORS.md' || filename === 'MAINTAINERS.md') {
      path = 'CONTRIBUTORS.toml'
    }
    else if (rootFileList.includes(filename)) {
      path = filename
    }
    else if (docsFileList.includes(filename)) {
      path = "docs/" + filename
    }
    else {
      const dotIndex = filename.lastIndexOf('.');
      let name = filename.slice(0, dotIndex);
      // const extension = filename.slice(dotIndex + 1);
      path = 'src/' + name.replace(/\./g, '/') + '.lagda.md';
    }

    const prefixedHref =
      'https://github.com/UniMath/agda-unimath/edit/master/' + path;
    link.setAttribute('href', prefixedHref);
  }
} else {
  console.error('Could not find a link with the class href-git-edit-button');
}
