import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.TreeMap;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;

/** Export only a successfully checked root module's concrete syntax tree. */
public final class ProverSyntaxTree {
    private static final Map<Integer, String> names = new TreeMap<>();

    private static String quoted(String text) {
        StringBuilder out = new StringBuilder("\"");
        for (char c : text.toCharArray()) {
            if (c == '"' || c == '\\') out.append('\\').append(c);
            else if (c < 32) out.append(String.format("\\u%04x", (int)c));
            else out.append(c);
        }
        return out.append('"').toString();
    }

    private static void write(TreeNode node, StringBuilder out) {
        out.append("{\"kind\":").append(quoted(names.getOrDefault(node.getKind(), "token")));
        out.append(",\"image\":").append(quoted(node.getImage()));
        out.append(",\"start\":[").append(node.getLocation().beginLine()).append(',')
           .append(node.getLocation().beginColumn()).append(']');
        out.append(",\"end\":[").append(node.getLocation().endLine()).append(',')
           .append(node.getLocation().endColumn()).append(']');
        out.append(",\"children\":[");
        TreeNode[] children = node.heirs();
        if (children != null) for (int i = 0; i < children.length; i++) {
            if (i > 0) out.append(',');
            write(children[i], out);
        }
        out.append("]}");
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) throw new IllegalArgumentException("module.tla output.json");
        Path destination = Path.of(args[1]);
        if (Files.exists(destination)) throw new IllegalArgumentException("Output already exists");
        SpecObj spec = new SpecObj(args[0]);
        int result = SANY.frontEndMain(spec, args[0], System.err);
        if (result != 0 || spec.getErrorLevel() != 0 || spec.getRootModule() == null
                || !spec.getInitErrors().isSuccess() || !spec.getParseErrors().isSuccess()
                || !spec.getSemanticErrors().isSuccess()) {
            System.err.println("PROVER_TREE_REJECTED");
            System.exit(2);
        }
        for (Field f : SyntaxTreeConstants.class.getFields()) {
            if (f.getType() == int.class && f.getName().startsWith("N_"))
                names.put(f.getInt(null), f.getName());
        }
        StringBuilder out = new StringBuilder();
        write(spec.getRootParseUnit().getParseTree(), out);
        Files.writeString(destination, out.append('\n').toString(), StandardCharsets.UTF_8);
        System.out.println("PROVER_TREE_COMPLETE");
    }
}
