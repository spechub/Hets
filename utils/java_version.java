/*
 * Determine your JDK
 */

/**
 *
 * @author luecke
 */
public class java_version {

    /**
     * @param None
     */
    public static void main(String[] args) {
        String vendor = System.getProperty("java.vm.vendor");
        String rt_name = System.getProperty("java.runtime.name");
        String vm_version = System.getProperty("java.vm.version");
        System.out.println(vendor + " " + rt_name + " " + vm_version);
    }

}
