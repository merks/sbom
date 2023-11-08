package org.eclipse.cbi.p2repo.sbom;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import javax.xml.namespace.NamespaceContext;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.cyclonedx.BomGeneratorFactory;
import org.cyclonedx.CycloneDxSchema;
import org.cyclonedx.generators.json.BomJsonGenerator;
import org.cyclonedx.generators.xml.AbstractBomXmlGenerator;
import org.cyclonedx.generators.xml.BomXmlGenerator;
import org.cyclonedx.model.Bom;
import org.cyclonedx.model.Component;
import org.cyclonedx.model.Component.Scope;
import org.cyclonedx.model.Dependency;
import org.cyclonedx.model.ExternalReference;
import org.cyclonedx.model.Hash;
import org.cyclonedx.model.License;
import org.cyclonedx.model.LicenseChoice;
import org.cyclonedx.model.Property;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.equinox.internal.p2.artifact.repository.simple.SimpleArtifactRepository;
import org.eclipse.equinox.p2.core.ProvisionException;
import org.eclipse.equinox.p2.internal.repository.tools.AbstractApplication;
import org.eclipse.equinox.p2.internal.repository.tools.RepositoryDescriptor;
import org.eclipse.equinox.p2.metadata.IArtifactKey;
import org.eclipse.equinox.p2.metadata.IInstallableUnit;
import org.eclipse.equinox.p2.metadata.IRequirement;
import org.eclipse.equinox.p2.metadata.expression.IMatchExpression;
import org.eclipse.equinox.p2.query.IQuery;
import org.eclipse.equinox.p2.query.QueryUtil;
import org.eclipse.equinox.p2.repository.artifact.ArtifactKeyQuery;
import org.eclipse.equinox.p2.repository.artifact.IArtifactDescriptor;
import org.eclipse.equinox.p2.repository.artifact.IArtifactRepositoryManager;
import org.eclipse.equinox.p2.repository.metadata.IMetadataRepository;
import org.eclipse.equinox.p2.repository.metadata.IMetadataRepositoryManager;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import com.ctc.wstx.stax.WstxOutputFactory;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.xml.XmlFactory;

@SuppressWarnings("restriction")
public class SBOMApplication implements IApplication {

	private static final Comparator<IArtifactKey> ARTIFACT_COMPARATOR = new Comparator<IArtifactKey>() {
		@Override
		public int compare(IArtifactKey o1, IArtifactKey o2) {
			int result = o1.getClassifier().compareTo(o2.getClassifier());
			if (result == 0) {
				result = o1.getId().compareTo(o2.getId());
				if (result == 0) {
					result = o1.getVersion().compareTo(o2.getVersion());
				}
			}
			return result;
		}
	};

	private static final List<String> ALGORITHMS = List.of("MD5", "SHA-1", "SHA-256", "SHA-512", "SHA-384", "SHA3-384",
			"SHA3-256", "SHA3-512");

	@Override
	public Object start(IApplicationContext context) throws Exception {
		new AbstractApplication() {
			@Override
			public IStatus run(IProgressMonitor monitor) throws ProvisionException {
				List<String> args = new ArrayList<>(
						Arrays.asList((String[]) context.getArguments().get("application.args")));
				URI uri = URI.create(args.get(0));

				IArtifactRepositoryManager artifactRepositoryManager = getArtifactRepositoryManager();
				IMetadataRepositoryManager metadataRepositoryManager = getMetadataRepositoryManager();
				RepositoryDescriptor repositoryDescriptor = new RepositoryDescriptor();
				repositoryDescriptor.setLocation(uri);
				addSource(repositoryDescriptor);
				IMetadataRepository metadataRepository = metadataRepositoryManager.loadRepository(uri, monitor);
				SimpleArtifactRepository artifactRepository = (SimpleArtifactRepository) artifactRepositoryManager
						.loadRepository(uri, monitor);
				Set<IInstallableUnit> ius = metadataRepository.query(QueryUtil.ALL_UNITS, monitor).toSet();

				Map<IArtifactKey, Set<IInstallableUnit>> artifactIUs = new TreeMap<IArtifactKey, Set<IInstallableUnit>>(
						ARTIFACT_COMPARATOR);

				Map<IInstallableUnit, IInstallableUnit> featureJarsToFeatures = new HashMap<IInstallableUnit, IInstallableUnit>();
				Map<IInstallableUnit, IInstallableUnit> featuresToFeatureJars = new HashMap<IInstallableUnit, IInstallableUnit>();
				for (IInstallableUnit iu : ius) {
					Collection<IArtifactKey> keys = iu.getArtifacts();
					if (keys.isEmpty()) {
						// System.err.println("##" + iu);
					} else {
						for (IArtifactKey key : keys) {
							artifactIUs.computeIfAbsent(key, k -> new TreeSet<>()).add(iu);
							String id = iu.getId();
							if (id.endsWith(".feature.jar")) {
								IQuery<IInstallableUnit> iuQuery = QueryUtil
										.createIUQuery(id.replaceAll(".jar$", ".group"), iu.getVersion());
								Set<IInstallableUnit> set = metadataRepository.query(iuQuery, monitor).toSet();
								if (set.size() != 1) {
									System.err.println("###");
								} else {
									IInstallableUnit feature = set.iterator().next();
									featureJarsToFeatures.put(iu, feature);
									featuresToFeatureJars.put(feature, iu);
								}
							}
						}
					}
				}

				Set<IArtifactKey> allArtifacts = artifactRepository.query(ArtifactKeyQuery.ALL_KEYS, monitor).toSet();
				for (IArtifactKey key : allArtifacts) {
					if (!artifactIUs.containsKey(key)) {
						// System.err.println("###");

					}
				}

				Bom bom = new Bom();

				Map<IInstallableUnit, Component> iuComponents = new LinkedHashMap<>();
				for (var entry : artifactIUs.entrySet()) {
					IArtifactKey key = entry.getKey();

					Set<IInstallableUnit> ius2 = entry.getValue();
					if (ius2.size() > 1) {
						// System.err.println("###");

					}

					IInstallableUnit iu = ius2.iterator().next();

					Component component = new Component();
					component.setName(iu.getId());
					component.setType(Component.Type.LIBRARY);
					component.setVersion(iu.getVersion().toString());
					component.setScope(Scope.REQUIRED);

					String name = iu.getProperty(IInstallableUnit.PROP_NAME, null);
					if (name != null) {
						component.setDescription(name);
					}

					String provider = iu.getProperty(IInstallableUnit.PROP_PROVIDER, null);
					if (provider != null) {
						component.setPublisher(provider);
					}

					Map<String, String> properties = iu.getProperties();
					for (var property : properties.entrySet()) {
						Property property2 = new Property();
						String key2 = property.getKey();
						String value = property.getValue();
						if (!"df_LT.license".equals(key2) && !"df_LT.copyright".equals(key2)
								&& !value.startsWith("%")) {
							property2.setName(key2);
							property2.setValue(value);
							component.addProperty(property2);
						}
					}

					IArtifactDescriptor[] artifactDescriptors = artifactRepository.getArtifactDescriptors(key);
					for (IArtifactDescriptor artifactDescriptor : artifactDescriptors) {
						String format = artifactDescriptor.getProperty(IArtifactDescriptor.FORMAT);
						if (format == null) {
							URI location = artifactRepository.getLocation(artifactDescriptor);
							component.setPurl(location.toString());
							component.setBomRef(location.toString());
							ByteArrayOutputStream out = new ByteArrayOutputStream();
							artifactRepository.getRawArtifact(artifactDescriptor, out, monitor);
							byte[] bytes = out.toByteArray();
							for (String algorithm : ALGORITHMS) {
								Hash hash = new Hash(algorithm, computeHash(algorithm, bytes));
								component.addHash(hash);
							}

							if (bytes.length > 2 && bytes[0] == 0x50 && bytes[1] == 0x4B) {
								processJar(component, bytes);
							}

							break;
						}
					}

					bom.addComponent(component);

					iuComponents.put(iu, component);

				}

				for (var entry2 : iuComponents.entrySet()) {

					IInstallableUnit iu = entry2.getKey();
					Component component = entry2.getValue();

					IInstallableUnit feature = featureJarsToFeatures.get(iu);
					if (feature != null) {
						iu = feature;
					}

					String componentBomRef = component.getBomRef();
					Dependency dependency = new Dependency(componentBomRef);
					bom.addDependency(dependency);

					for (IRequirement requirement : iu.getRequirements()) {
						int min = requirement.getMin();
						IMatchExpression<IInstallableUnit> matches = requirement.getMatches();
						Set<IInstallableUnit> requiredIUs = metadataRepository
								.query(QueryUtil.createMatchQuery(matches), monitor).toSet();
						if (requiredIUs.isEmpty()) {
							if (min != 0) {
								System.err.println("###!" + requirement);
							}
						} else {
							for (IInstallableUnit requiredIU : requiredIUs) {
								IInstallableUnit featureJar = featuresToFeatureJars.get(requiredIU);
								Component requiredComponent = iuComponents
										.get(featureJar == null ? requiredIU : featureJar);
								if (requiredComponent == null) {
									System.err.println("###>" + requiredIU);
								} else {
									String bomRef = requiredComponent.getBomRef();
									if (!componentBomRef.equals(bomRef)) {
										dependency.addDependency(new Dependency(bomRef));
									}
								}
							}
						}
					}
				}

				try {
					BomXmlGenerator xmlGenerator = createXml(CycloneDxSchema.Version.VERSION_15, bom);
					String xmlString = xmlGenerator.toXmlString();
					System.out.println(xmlString);
				} catch (Exception ex) {
					throw new RuntimeException(ex);
				}

				// IMetadataRepository compositeMetadataRepository =
				// getCompositeMetadataRepository();
				// IArtifactRepository compositeArtifactRepository =
				// getCompositeArtifactRepository();
				// test();
				return null;
			}
		}.run(new NullProgressMonitor());

		return null;
	}

	private static final Pattern MAVEN_POM_PATTERN = Pattern.compile("META-INF/maven/[^/]+/[^/]+/pom.xml");

	private void processJar(Component component, byte[] bytes) {
		try (var zip = new ZipInputStream(new ByteArrayInputStream(bytes))) {
			ZipEntry entry;
			while ((entry = zip.getNextEntry()) != null) {
				String name = entry.getName();
				// System.err.println("###" + name);
				if (MAVEN_POM_PATTERN.matcher(name).matches()) {
					byte[] allBytes = zip.readAllBytes();
					processPOM(component, allBytes);
					// System.err.println("###");
				}
				zip.closeEntry();
			}
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	static final XPathFactory XPATH_FACTORY = XPathFactory.newInstance();

	private static List<Element> evaluate(Node node, String expression) {
		XPath xPath = XPATH_FACTORY.newXPath();
		try {
			NamespaceContext namespaceContext = new NamespaceContext() {
				@Override
				public Iterator<String> getPrefixes(String namespaceURI) {
					return null;
				}

				@Override
				public String getPrefix(String namespaceURI) {
					return null;
				}

				@Override
				public String getNamespaceURI(String prefix) {
					return "http://maven.apache.org/POM/4.0.0";
				}
			};

			xPath.setNamespaceContext(namespaceContext);

			var nodeList = (NodeList) xPath.compile(expression).evaluate(node, XPathConstants.NODESET);
			var result = new ArrayList<Element>();
			for (int i = 0, length = nodeList.getLength(); i < length; ++i) {
				result.add((Element) nodeList.item(i));
			}
			return result;
		} catch (XPathExpressionException e) {
			throw new IllegalArgumentException(expression);
		}
	}

	private static String getText(Element element, String name) {
		var nodeList = element.getElementsByTagName(name);
		if (nodeList.getLength() > 0) {
			return nodeList.item(0).getTextContent();
		}
		return null;
	}

	private void processPOM(Component component, byte[] bytes) {
		var factory = DocumentBuilderFactory.newInstance();
		factory.setNamespaceAware(true);
		factory.setValidating(false);
		try {
			var builder = factory.newDocumentBuilder();
			String string = new String(bytes, StandardCharsets.UTF_8);
			// System.err.println("###" + string);
			Document document = builder.parse(new InputSource(new ByteArrayInputStream(bytes)));

			List<Element> licenses = evaluate(document, "//pom:license");
			if (!licenses.isEmpty()) {
				LicenseChoice licenseChoice = new LicenseChoice();
				for (Element element : licenses) {
					String name = getText(element, "name");
					License license = new License();
					license.setName(name);
					String url = getText(element, "url");
					license.setUrl(url);
					licenseChoice.addLicense(license);
				}

				component.setLicenseChoice(licenseChoice);
			}

			List<Element> scms = evaluate(document, "//pom:scm/pom:url");
			for (Element element : scms) {
				String url = element.getTextContent();
				if (url != null) {
					ExternalReference externalReference = new ExternalReference();
					externalReference.setType(ExternalReference.Type.VCS);
					externalReference.setUrl(url);
					component.addExternalReference(externalReference);
				}
			}
		} catch (ParserConfigurationException | SAXException | IOException ex) {
			throw new RuntimeException(ex);
		}
	}

	private String computeHash(String algorithm, byte[] bytes) {
		try {
			MessageDigest digest = MessageDigest.getInstance(algorithm);
			byte[] result = digest.digest(bytes);
			return HexFormat.of().formatHex(result);
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	private void test() {
		try {
			ExternalReference extRef = new ExternalReference();
			extRef.setType(ExternalReference.Type.BOM);
			extRef.setUrl("https://example.org/support/sbom/portal-server/1.0.0");
			extRef.setComment("An external SBOM that describes what this component includes");
			Hash md5 = new Hash(Hash.Algorithm.MD5, "2cd42512b65500dc7ba0ff13490b0b73");
			Hash sha1 = new Hash(Hash.Algorithm.SHA1, "226247b40160f2892fa4c7851b5b913d5d10912d");
			Hash sha256 = new Hash(Hash.Algorithm.SHA_256,
					"09a72795a920c1a9c0209cfb8395f8d97089832d249cba8c0938a3423b3ed1d1");
			extRef.setHashes(Arrays.asList(md5, sha1, sha256));

			Component component = new Component();
			component.setGroup("org.example");
			component.setName("mylibrary");
			component.setType(Component.Type.LIBRARY);
			component.setVersion("1.0.0");
			component.addExternalReference(extRef);

			Bom bom = new Bom();
			bom.addComponent(component);

			if (Boolean.FALSE) {
				BomXmlGenerator xmlGenerator = BomGeneratorFactory.createXml(CycloneDxSchema.Version.VERSION_15, bom);
				ObjectMapper mapper = ((AbstractBomXmlGenerator) xmlGenerator).getMapper();
				XmlFactory factory = (XmlFactory) mapper.getFactory();
				WstxOutputFactory f = new WstxOutputFactory();
				f.getConfig().enableAutomaticNamespaces(true);
				factory.setXMLOutputFactory(f);
				String xmlString = xmlGenerator.toXmlString();
				System.out.println(xmlString);
			}

			{
				BomXmlGenerator xmlGenerator = createXml(CycloneDxSchema.Version.VERSION_15, bom);
				String xmlString = xmlGenerator.toXmlString();
				System.out.println(xmlString);
			}

			{
				BomJsonGenerator jsonGenerator = BomGeneratorFactory.createJson(CycloneDxSchema.Version.VERSION_15,
						bom);
				String jsonString = jsonGenerator.toJsonString();
				System.out.println(jsonString);
			}
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	private BomXmlGenerator createXml(CycloneDxSchema.Version version, Bom bom) {
		Thread thread = Thread.currentThread();
		ClassLoader contextClassLoader = thread.getContextClassLoader();
		String propertyName = javax.xml.stream.XMLOutputFactory.class.getName();
		String property = System.getProperty(propertyName);
		try {
			System.setProperty(propertyName, WstxOutputFactory.class.getName());
			thread.setContextClassLoader(getClass().getClassLoader());
			return BomGeneratorFactory.createXml(version, bom);
		} finally {
			if (property == null) {
				System.clearProperty(propertyName);
			} else {
				System.setProperty(propertyName, property);
			}
			thread.setContextClassLoader(contextClassLoader);
		}
	}

	@Override
	public void stop() {
		// TODO Auto-generated method stub

	}
}
